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

    def introduce(self, node):
        return "SELECT true val UNION ALL SELECT false UNION ALL SELECT null"

    def td_node_extra_columns(self):
        if self.count:
            return [("model_count", "NUMERIC")]
        return []

    def candidate_extra_cols(self, node):
        if self.count:
            return ["{}::numeric AS model_count".format(
                " * ".join(set([var2cnt(node, v) for v in node.vertices] +
                               [node2cnt(n) for n in node.children])) if node.children else "1"
            )]
        return []

    def assignment_extra_cols(self, node):
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
        if(self.count):
            return " WHERE model_count > 0"
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

    def set_input(self, num_vars, num_rules, non_nested, elp):
        self.num_vars = num_vars
        self.num_rules = num_rules
        self.epistemic_atoms = elp.epistemic_atoms
        self.epistemic_not_atoms = elp.epistemic_not_atoms
        self.non_nested = non_nested
        self.var_rule_dict = elp.var_rule_dict
        self.var_symbol_dict = elp.var_symbol_dict
        self.extra_atoms = elp.extra_atoms
        self.choice_rules = elp.choice_rules
        self.epistemic_constraints = elp.epistemic_constraints

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
            choice_rules = [cr for cr in self.choice_rules if cr['head'][0] in node.all_vertices]
            rules = list(covered_rules)
            reduct = rules.copy()
            pn_constraint = {'head': [], 'body': []}
            undecided_constraints = []
            epistemic_constraints = {}

            for i, v in enumerate(vals):
                where.append("{} = {}".format(cols[i], v) if v != None else "{} is {}".format(cols[i], "null"))
                n = node.vertices[i]
                # build reduct
                reduct = get_subjective_reduct(reduct, self.var_symbol_dict, self.extra_atoms, n, v)
                if v != None:
                    # use the opposite and check for empty set
                    # TODO: check if still epistemic and build epistemic constraint (?)
                    if v:
                        pn_constraint['body'].append(n)
                        # constraints.append({'head': [], 'body': [(-1) * n]})
                    else:
                        pn_constraint['body'].append((-1) * n)
                        # constraints.append({'head': [], 'body': [(-1) * n]})
                else:
                    # undecided
                    undecided_constraints.append(({'head': [], 'body': [n]}, {'head': [], 'body': [(-1) * n]}))

            epistemic_atoms = self.epistemic_atoms.intersection(node.all_vertices) - set(node.vertices)
            non_nested = self.non_nested.intersection(node.all_vertices) - set(node.vertices)

            logger.info(
                f"Problem {self.id}: Calling recursive for bag {node.id}: {num_vars} {len(reduct)} {len(epistemic_atoms)} {self.depth+1}")

            epistemic_constraints = get_relevant_constraints(self.epistemic_constraints, node.all_vertices, self.extra_atoms)
            _sub_epistemic = len(epistemic_atoms) > 0 or not constraints_is_empty(epistemic_constraints)

            if _sub_epistemic:
                epistemic_constraints = get_epistemic_constraints(epistemic_constraints, pn_constraint, undecided_constraints)
                sat = self.rec_func(node.all_vertices, reduct, choice_rules, self.extra_atoms,
                                    self.var_symbol_dict,
                                    non_nested, epistemic_atoms, self.epistemic_not_atoms, epistemic_constraints, self.depth + 1,
                                    **self.kwargs)

            else:
                kwargs_sat = self.kwargs.copy()
                kwargs_sat['count_solutions'] = False

                # base reduct satisfiable?
                # count: number of wv's for reduct
                # idea: remove this call if there is a least one undecided literal
                sat = self.rec_func(node.all_vertices, reduct, choice_rules, self.extra_atoms,
                                    self.var_symbol_dict,
                                    non_nested, epistemic_atoms, self.epistemic_not_atoms, epistemic_constraints, self.depth+1, **kwargs_sat)

                # check for empty set -> cf. AAAI Listing 1 Line 4.1
                # only if there are positive/negative values (and therefore constraints)
                if (True in vals or False in vals):
                    sat = sat and not (
                        self.rec_func(node.all_vertices, reduct + [pn_constraint], choice_rules, self.extra_atoms,
                                      self.var_symbol_dict,
                                      non_nested, epistemic_atoms, self.epistemic_not_atoms, epistemic_constraints, self.depth+1, **kwargs_sat))

                # use epistemic constraints to test undecided atoms
                if len(undecided_constraints) > 0:
                    epistemic_constraints = get_epistemic_constraints(epistemic_constraints, None, undecided_constraints)
                    sat = sat and self.rec_func(node.all_vertices, reduct, choice_rules, self.extra_atoms,
                                        self.var_symbol_dict,
                                        non_nested, epistemic_atoms, self.epistemic_not_atoms, epistemic_constraints,
                                        self.depth + 1,
                                        **kwargs_sat)

                # for all undecided literals check if both constraints ⊥←b and ⊥←¬b have answer sets
                # for constraint in undecided_constraints:
                #     sat = sat and self.rec_func(node.all_vertices, reduct + [constraint[0]], choice_rules,
                #                                 self.extra_atoms,
                #                                 self.var_symbol_dict,
                #                                 non_nested, epistemic_atoms, self.epistemic_not_atoms, epistemic_constraints, self.depth+1, **kwargs_sat)
                #     sat = sat and self.rec_func(node.all_vertices, reduct + [constraint[1]], choice_rules,
                #                                 self.extra_atoms,
                #                                 self.var_symbol_dict,
                #                                 non_nested, epistemic_atoms, self.epistemic_not_atoms, epistemic_constraints, self.depth+1, **kwargs_sat)

                if self.count:
                    sat = 1 if sat else 0

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
            # logger.info("Problem has %d world view(s)", self.model_count)
        else:
            is_sat = self.db.replace_dynamic_tabs(f"(select exists(select 1 from {root_tab}))")
            self.db.ignore_next_praefix()
            self.sat = self.db.update("problem_elp", ["is_sat"], [is_sat], [f"ID = {self.id}"], "is_sat")[0]
            # logger.info("Problem is %s", "SAT" if self.sat else "UNSAT")


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
        ),
        "--input-format": dict(
            dest="input_format",
            help="Input format: &k{} elp format, 3qbf qdimacs",
            choices=["lp", "qdimacs"],
            default="lp"
        )
    }
)
