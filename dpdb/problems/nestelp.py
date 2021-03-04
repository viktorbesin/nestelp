# -*- coding: future_fstrings -*-
import logging
import subprocess
from collections import defaultdict
from concurrent.futures import ThreadPoolExecutor, as_completed

# from nesthdb.solve import nesthdb
from dpdb.abstraction import Abstraction
from dpdb.problem import *
from dpdb.reader import CnfReader
from dpdb.writer import StreamWriter, FileWriter, normalize_cnf
from .sat_util import *
from .elp_util import *

logger = logging.getLogger(__name__)


def var2col2(node, var, minors):
    # if node.is_minor(var):
    if var in minors:
        return "{}.val".format(var2tab_alias(node, var))
    else:
        return f"v{var}"


def lit2var2(node, lit, minors):
    return var2col2(node, abs(lit), minors)


def lit2expr2(node, lit, minors):
    if lit > 0:
        return lit2var2(node, lit, minors)
    else:
        return "NOT {}".format(lit2var2(node, lit, minors))


class NestElp(Problem):
    @classmethod
    def keep_cfg(cls):
        return ["asp_encodings", "sat_solver"]

    def __init__(self, name, pool, max_solver_threads=12, inner_vars_threshold=0, store_formula=False, **kwargs):
        super().__init__(name, pool, **kwargs)
        self.store_formula = store_formula
        # self.abstr = Abstraction(self.sub_procs, **kwargs)
        # self.interrupt_handler.append(self.abstr.interrupt)
        self.max_solver_threads = max_solver_threads
        self.store_all_vertices = True
        self.inner_vars_threshold = inner_vars_threshold
        self.count = kwargs.get('count_solutions')

    def td_node_column_def(self, var):
        return (var2col(var), "BOOLEAN")

    def td_node_extra_columns(self):
        if self.count:
            return [("model_count","NUMERIC")]
        return []

    def candidate_extra_cols(self,node):
        if self.count:
            return ["{}::numeric AS model_count".format(
                    " * ".join(set([var2cnt(node,v) for v in node.vertices] +
                                   [node2cnt(n) for n in node.children])) if node.children else "1"
                    )]
        return []

    def assignment_extra_cols(self,node):
        if self.count:
            return ["sum(model_count)::numeric AS model_count"]
        return []

    def candidates_select(self, node):
        extra_proj = []
        q = ""

        if any(node.needs_introduce(v) for v in node.vertices):
            q += "WITH introduce AS ({}) ".format(self.introduce(node))

        q += "SELECT {}".format(
            ",".join([var2tab_col(node, v) for v in node.vertices + extra_proj]),
        )

        extra_cols = self.candidate_extra_cols(node)
        if extra_cols:
            q += "{}{}".format(", " if node.vertices else "", ",".join(extra_cols))

        if node.vertices or node.children:
            q += " FROM {}".format(
                ",".join(
                    set(["{} {}".format(var2tab(node, v), var2tab_alias(node, v)) for v in node.vertices + extra_proj] +
                        ["{} {}".format(node2tab(n), node2tab_alias(n)) for n in node.children]))
            )

        if len(node.children) > 1:
            q += " {} ".format(self.join(node))

        return q

    def filter(self, node):
        return ""

    def setup_extra(self):
        def create_tables():
            self.db.ignore_next_praefix()
            if self.count:
                self.db.create_table("problem_elp_count", [
                    ("id", "INTEGER NOT NULL PRIMARY KEY REFERENCES PROBLEM(id)"),
                    ("num_vars", "INTEGER NOT NULL"),
                    ("num_rules", "INTEGER NOT NULL"),
                    ("model_count", "NUMERIC")
                ])
            else:
                self.db.create_table("problem_elp", [
                    ("id", "INTEGER NOT NULL PRIMARY KEY REFERENCES PROBLEM(id)"),
                    ("num_vars", "INTEGER NOT NULL"),
                    ("num_rules", "INTEGER NOT NULL"),
                    ("is_sat", "BOOLEAN")
                ])
            if "faster" not in self.kwargs or not self.kwargs["faster"]:
                self.db.create_table("epistemic_atoms", [
                    ("id", "INTEGER NOT NULL REFERENCES PROBLEM(id)"),
                    ("var", "INTEGER NOT NULL")
                ])
                self.db.create_pk("epistemic_atoms", ["id", "var"])

        # TODO: adapt to elp
        def insert_data():
            self.db.ignore_next_praefix()
            if self.count:
                self.db.insert("problem_elp_count", ("id", "num_vars", "num_rules"),
                               (self.id, self.num_vars, self.num_rules))
            else:
                self.db.insert("problem_elp", ("id", "num_vars", "num_rules"),
                               (self.id, self.num_vars, self.num_rules))
            if "faster" not in self.kwargs or not self.kwargs["faster"]:
                for ea in self.epistemic_atoms:
                    self.db.insert("epistemic_atoms", ("id", "var"), (self.id, ea))
                self.db.ignore_next_praefix()
                self.db.insert("problem_option", ("id", "name", "value"),
                               (self.id, "store_formula", self.store_formula))
                # TODO: store rules
                # if self.store_formula:
                #     store_clause_table(self.db, self.clauses)

        create_tables()
        insert_data()

    # TODO
    def prepare_input(self, fname):
        input = CnfReader.from_file(fname)
        self.num_vars = input.num_vars
        self.num_clauses = input.num_clauses
        self.clauses = input.clauses
        self.projected = list(input.projected)
        self.var_clause_dict = defaultdict(set)
        # logger.debug("{} vars, {}={} clauses", input.num_vars, input.num_clauses, len(input.clauses))
        num_vars, edges, adj = cnf2primal(input.num_vars, input.clauses, self.var_clause_dict, True)
        return self.abstr.abstract(num_vars, edges, adj, self.projected)

    def set_recursive(self, func, depth):
        self.rec_func = func
        self.depth = depth

    def set_input(self, num_vars, num_rules, epistemic_atoms, epistemic_non_atoms, non_nested, var_rule_dict, facts,
                  var_symbol_dict, extra_atoms):
        self.num_vars = num_vars
        self.num_rules = num_rules
        self.epistemic_atoms = epistemic_atoms
        self.epistemic_non_atoms = epistemic_non_atoms
        self.non_nested = non_nested
        self.var_rule_dict = var_rule_dict
        self.facts = facts
        self.var_symbol_dict = var_symbol_dict
        self.extra_atoms = extra_atoms

    def after_solve_node(self, node, db):
        cols = [var2col(c) for c in node.vertices]
        executor = ThreadPoolExecutor(self.max_solver_threads)
        futures = []
        rules = covered_rules(self.var_rule_dict, node.all_vertices, self.extra_atoms)
        if len(rules) == 0:
            return
        for r in db.select_all(f"td_node_{node.id}", cols):
            if not self.interrupted:
                # if len(node.all_vertices) - len(node.vertices) > self.inner_vars_threshold: # only if there is an inner problem to solve
                futures.append(executor.submit(self.solve_elp, node, db, cols, r, rules))
        for future in as_completed(futures):
            if future.exception():
                raise future.exception()
        executor.shutdown(wait=True)

    def solve_elp(self, node, db, cols, vals, covered_rules):
        if self.interrupted:
            return
        try:
            where = []
            num_vars = len(node.all_vertices)
            rules = list(covered_rules)
            for i, v in enumerate(vals):
                if v != None:
                    where.append("{} = {}".format(cols[i], v))
                    n = node.vertices[i]

                    if v:
                        rules.append({'head': [], 'body': [n]})
                    else:
                        rules.append({'head': [], 'body': [(-1) * n]})

            epistemic_atoms = self.epistemic_atoms.intersection(node.all_vertices) - set(node.vertices)

            non_nested = self.non_nested.intersection(node.all_vertices) - set(node.vertices)
            logger.info(
                f"Problem {self.id}: Calling recursive for bag {node.id}: {num_vars} {len(rules)} {len(epistemic_atoms)}")

            sat = self.rec_func(node.all_vertices, rules, self.facts, self.extra_atoms, self.var_symbol_dict,
                                non_nested, epistemic_atoms, self.depth + 1, **self.kwargs)
            if not self.interrupted:
                if self.count:
                    db.update(f"td_node_{node.id}", ["model_count"], ["model_count * {}::numeric".format(sat)], where)
                    db.commit()
                else:
                    if not sat:
                        db.delete(f"td_node_{node.id}", where)
                        db.commit()
        except Exception as e:
            raise e

    def after_solve(self):
        if self.interrupted:
            return
        root_tab = f"td_node_{self.td.root.id}"
        if self.count:
            sum_count = self.db.replace_dynamic_tabs(f"(select coalesce(sum(model_count),0) from {root_tab})")
            self.db.ignore_next_praefix()
            self.model_count = self.db.update("problem_elp_count", ["model_count"], [sum_count], [f"ID = {self.id}"], "model_count")[0]
            logger.info("Problem has %d answer sets", self.model_count)
        else:
            is_sat = self.db.replace_dynamic_tabs(f"(select exists(select 1 from {root_tab}))")
            self.db.ignore_next_praefix()
            self.sat = self.db.update("problem_elp", ["is_sat"], [is_sat], [f"ID = {self.id}"], "is_sat")[0]
            logger.info("Problem is %s", "SAT" if self.sat else "UNSAT")


def var2cnt(node, var):
    if node.needs_introduce(var):
        return "1"
    else:
        return "{}.model_count".format(var2tab_alias(node, var))


def node2cnt(node):
    return "{}.model_count".format(node2tab_alias(node))

args.specific[NestElp] = dict(
)

args.nested[NestElp] = dict(
    help="Solve nested ELP instances",
    options={
        "--count": dict(
            action="store_true",
            dest="count_solutions",
            help="Count the solutions for the problem"
        )
    }

)
