#!/usr/bin/python3
# -*- coding: future_fstrings -*-
import importlib
import logging
import os
import sys
import inspect
import tempfile
from collections import defaultdict

src_path = os.path.abspath(os.path.realpath(inspect.getfile(inspect.currentframe())))
sys.path.insert(0, os.path.realpath(os.path.join(src_path, '..')))

src_path = os.path.realpath(os.path.join(src_path, '../lib'))
libs = ['eclingo/eclingo']

if src_path not in sys.path:
    for lib in libs:
        sys.path.insert(0, os.path.join(src_path, lib))

from common import *
from dpdb.abstraction import MinorGraph, ClingoControl
from dpdb.db import BlockingThreadedConnectionPool, DBAdmin, DEBUG_SQL, setup_debug_sql
from dpdb.problems.nestpmc import NestPmc
from dpdb.problems.nestelp import NestElp
from dpdb.problems.sat_util import *
from dpdb.problems.elp_util import *
from dpdb.reader import CnfReader, ELPReader, QuantitiveSelectionReader
from dpdb.writer import FileWriter, StreamWriter, denormalize_cnf, normalize_cnf

logger = logging.getLogger("nestHDB")
setup_debug_sql()

class Formula:
    def __init__(self, vars, clauses, projected=None):
        self.vars = vars
        self.num_vars = len(vars)
        self.clauses = clauses
        self.num_clauses = len(clauses)
        self.projected = projected
        self.var_clause_dict = defaultdict(set)

    @classmethod
    def from_file(cls, fname):
        input = CnfReader.from_file(fname)
        # uncomment the following line for sharpsat solving
        #input.projected = set(range(1,input.num_vars+1)) - input.single_vars		#sharpsat!
        return cls(input.vars, input.clauses, input.projected)

class ELP:
    def __init__(self, atoms, rules, choice_rules, extra_atoms, epistemic_atoms, qr_atoms, epistemic_constraints, var_symbol_dict):
        self.atoms = atoms
        self.rules = rules
        self.choice_rules = choice_rules
        self.epistemic_atoms = epistemic_atoms
        self.var_symbol_dict = var_symbol_dict
        self.extra_atoms = extra_atoms
        self.epistemic_constraints = epistemic_constraints
        self.qr_atoms = qr_atoms

        self.var_rule_dict = defaultdict(set)

    @classmethod
    def from_file(cls, fname):
        if args.input_format == 'qdimacs':
            assert ('3qbf_parser' in cfg['nesthdb'])
            assert ('path' in cfg['nesthdb']['3qbf_parser'])
            parser = cfg['nesthdb']['3qbf_parser']['path']
            logging.info(f"Parsing 3QBF file using {parser}")
            with open(fname, mode='rb') as file_object:
                pparser = subprocess.Popen(parser, stdin=file_object, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL)
                input = ELPReader.from_stream(pparser.stdout)
                pparser.communicate()
                if (pparser.returncode != 0):
                    logger.error("Error while parsing .qdimacs file!")
                    sys.exit(1)
        else:
            input = ELPReader.from_file(fname)
        return cls(input.atoms, input.rules, input.choice_rules, input.extra_atoms, input.epistemic_atoms, set(), ELP.empty_constraints(), input.var_symbol_dict)

    @classmethod
    def empty_constraints(cls):
        return {'p': [], 'n': [], 'u': []}

class Graph:
    def __init__(self, nodes, edges, adj_list):
        self.nodes = nodes
        self.edges = edges
        self.adj_list = adj_list
        self.tree_decomp = None

    @property
    def num_nodes(self):
        return len(self.nodes)

    @property
    def num_edges(self):
        return len(self.edges)

    def abstract(self, non_nested):
        proj_out = self.nodes - non_nested
        mg = MinorGraph(self.nodes, self.adj_list, proj_out)
        mg.abstract()
        mg.add_cliques()
        self.nodes = mg.nodes
        self.edges = mg.edges
        self.adj_list = mg.adj_list
        self.mg = mg

    def normalize(self):
        self.nodes_normalized = set()
        self.edges_normalized = set()
        self.adj_list_normalized = {}
        self._node_map = {}
        self._node_rev_map = {}

        last = 0
        for n in self.nodes:
            last += 1
            self._node_map[n] = last
            self._node_rev_map[last] = n
            self.nodes_normalized.add(last)

        for e in self.edges:
            u = self._node_map[e[0]]
            v = self._node_map[e[1]]
            if u < v:
                self.edges_normalized.add((u,v))
            else:
                self.edges_normalized.add((v,u))

    def decompose(self, **kwargs):
        global cfg
        self.normalize()
        self.tree_decomp = decompose(self.num_nodes,self.edges_normalized,cfg["htd"],node_map=self._node_rev_map,minor_graph=self.mg,**kwargs)

interrupted = False
cache = {}
pos_cache = {}
neg_cache = {}

class Problem:
    @classmethod
    def prepare_instance(cls, fname, args):
        formula = Formula.from_file(fname)
        return cls(formula,formula.vars,**vars(args))

    def __init__(self, formula, non_nested, depth=0, **kwargs):
        self.formula = formula
        self.projected = formula.projected
        self.projected_orig = set(formula.projected)
        self.non_nested = non_nested
        self.non_nested_orig = non_nested
        self.maybe_sat = True
        self.models = None
        self.depth = depth
        self.kwargs = kwargs
        self.sub_problems = set()
        self.nested_problem = None
        self.active_process = None

    def preprocess(self):
        global cfg
        if "preprocessor" not in cfg["nesthdb"]:
            return # True, num_vars, vars, len(clauses), clauses, None
        cfg_prep = cfg["nesthdb"]["preprocessor"]
        preprocessor = [cfg_prep["path"]]
        if "args" in cfg_prep:
            preprocessor.extend(cfg_prep["args"].split(' '))
        self.active_process = ppmc = subprocess.Popen(preprocessor,stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL)
        clauses,proj_vars,num_vars,mapping,rev_mapping = normalize_cnf(self.formula.clauses, self.projected, True)
        StreamWriter(ppmc.stdin).write_cnf(self.formula.num_vars,clauses,normalize=False)
        ppmc.stdin.close()
        input = CnfReader.from_stream(ppmc.stdout,silent=True)
        ppmc.wait()
        ppmc.stdout.close()
        self.active_process = None
        if not input.error:
            self.maybe_sat = input.maybe_sat
            if not input.done:
                # fix corner case, where input.vars contains not all of range(1,input.max_vars+1)
                clauses, vars, proj_vars = denormalize_cnf(input.clauses,input.vars,proj_vars,rev_mapping)
                self.formula = Formula(vars,clauses)
                self.projected = proj_vars.intersection(vars)
                # remove single_clause_proj_vars, they are not needed/relevant and only waste resources!
                # consequently, these variables are treated as if they were never there, no 2 ** correction!
                _, singles, _ = denormalize_cnf((),input.single_vars,(),rev_mapping)
                self.projected_orig = self.projected_orig.difference(singles)
            else:
                # set models to 1 if instance was sat
                if len(self.projected) == 0:
                    self.models = 1
                # use result if instance was #sat
                elif self.projected.intersection(self.formula.vars) == self.formula.vars:
                    self.models = input.models
                # dont use result if instance was pmc
                else:
                    pass
        else:
            logger.debug("Pre-processor failed... ignoring result")

    def decompose_nested_primal(self):
        num_vars, edges, adj = cnf2primal(self.formula.num_vars, self.formula.clauses, self.formula.var_clause_dict, True)
        self.graph = Graph(set(self.formula.vars), edges, adj)
        logger.info(f"Primal graph #vertices: {num_vars}, #edges: {len(edges)}")
        self.graph.abstract(self.non_nested)
        logger.info(f"Nested primal graph #vertices: {self.graph.num_nodes}, #edges: {self.graph.num_edges}")
        self.graph.decompose(**self.kwargs)

    def choose_subset(self):
        global cfg
        cfg_asp = cfg["nesthdb"]["asp"]
        for enc in cfg_asp["encodings"]:
            if interrupted:
                return
            size = enc["size"]
            timeout = 30 if "timeout" not in enc else enc["timeout"]
            logger.debug("Running clingo %s for size %d and timeout %d", enc["file"],size,timeout)
            c = ClingoControl(self.graph.edges,self.non_nested)
            res = c.choose_subset(min(size,len(self.non_nested)),enc["file"],timeout)[2]
            if len(res) == 0:
                logger.warning("Clingo did not produce an answer set, fallback to previous result {}".format(self.non_nested))
            else:
                self.non_nested = set(res[0])
            logger.debug("Clingo done%s", " (timeout)" if c.timeout else "")
        assert(len(self.non_nested) > 0)

    def call_solver(self,type):
        global cfg

        logger.info(f"Call solver: {type} with #vars {self.formula.num_vars}, #clauses {len(self.formula.clauses)}, #projected {len(self.projected)}")

        cfg_str = f"{type}_solver"
        assert(cfg_str in cfg["nesthdb"])
        assert("path" in cfg["nesthdb"][cfg_str])
        local_cfg = cfg["nesthdb"][cfg_str]
        solver = [local_cfg["path"]]

        if "seed_arg" in local_cfg:
            solver.append(local_cfg["seed_arg"])
            solver.append(str(self.kwargs["runid"]))
        if "args" in local_cfg:
            solver.extend(local_cfg["args"].split(' '))
        if "output_parser" in local_cfg:
            solver_parser = local_cfg["output_parser"]
            reader_module = importlib.import_module("dpdb.reader")
            solver_parser_cls = getattr(reader_module, solver_parser["class"])
        else:
            solver_parser = {"class":"CnfReader","args":{"silent":True},"result":"models"}
            solver_parser_cls = CnfReader

        tmp = tempfile.NamedTemporaryFile().name
        with FileWriter(tmp) as fw:
            fw.write_cnf(self.formula.num_vars,self.formula.clauses,normalize=True, proj_vars=self.projected)
            for i in range(0,128,1):
                if interrupted:
                    return -1
                self.active_process = psat = subprocess.Popen(solver + [tmp], stdout=subprocess.PIPE)
                output = solver_parser_cls.from_stream(psat.stdout,**solver_parser["args"])
                psat.wait()
                psat.stdout.close()
                self.active_process = None
                if interrupted:
                    return -1
                result = int(getattr(output,solver_parser["result"]))
                if psat.returncode == 245 or psat.returncode == 250:
                    logger.debug("Retrying call to external solver, returncode {}, index {}".format(psat.returncode, i))
                else:
                    logger.debug("No Retry, returncode {}, result {}, index {}".format(psat.returncode, result, i))
                    break

        logger.info(f"Solver {type} result: {result}")
        return result
    
    def solve_classic(self):
        if interrupted:
            return -1
        # uncomment the following line for sharpsat solving
        #return self.call_solver("sharpsat")
        if self.formula.vars == self.projected:
            return self.call_solver("sharpsat")
        else:
            return self.call_solver("pmc")

    def final_result(self,result):
        len_old = len(self.projected_orig)
        len_new = len(self.projected)
        len_diff = len_old - len_new
        exp = 2**len_diff
        final = result * exp
        if not self.kwargs["no_cache"]:
            frozen_clauses = frozenset([frozenset(c) for c in self.formula.clauses])
            cache[frozen_clauses] = final
        return final

    def get_cached(self):
        frozen_clauses = frozenset([frozenset(c) for c in self.formula.clauses])
        if frozen_clauses in cache:
            return cache[frozen_clauses]
        else:
            return None

    def nestedpmc(self):
        global cfg

        pool = BlockingThreadedConnectionPool(1,cfg["db"]["max_connections"],**cfg["db"]["dsn"])
        problem_cfg = {}
        if "problem_specific" in cfg and "nestpmc" in cfg["problem_specific"]:
            problem_cfg = cfg["problem_specific"]["nestpmc"]
        if interrupted:
            return -1
        self.nested_problem = NestPmc("test",pool, **cfg["dpdb"], **flatten_cfg(problem_cfg, [], '_',NestPmc.keep_cfg()),**self.kwargs)
        if interrupted:
            return -1
        self.nested_problem.set_td(self.graph.tree_decomp)
        if interrupted:
            return -1
        self.nested_problem.set_recursive(self.solve_rec,self.depth)
        if interrupted:
            return -1
        self.nested_problem.set_input(self.graph.num_nodes,-1,self.projected,self.non_nested_orig,self.formula.var_clause_dict)
        if interrupted:
            return -1
        self.nested_problem.setup()
        if interrupted:
            return -1
        self.nested_problem.solve()
        if interrupted:
            return -1
        return self.nested_problem.model_count

    def solve(self):
        logger.info(f"Original #vars: {self.formula.num_vars}, #clauses: {self.formula.num_clauses}, #projected: {len(self.projected_orig)}, depth: {self.depth}")
        #self.preprocess()
        if self.maybe_sat == False:
            logger.info("Preprocessor UNSAT")
            return 0
        if self.models != None:
            logger.info(f"Solved by preprocessor: {self.models} models")
            return self.final_result(self.models)

        self.non_nested = self.non_nested.intersection(self.projected)
        logger.info(f"Preprocessing #vars: {self.formula.num_vars}, #clauses: {self.formula.num_clauses}, #projected: {len(self.projected)}")

        if not self.kwargs["no_cache"]:
            cached = self.get_cached()
            if cached != None:
                logger.info(f"Cache hit: {cached}")
                return cached

        if len(self.projected.intersection(self.formula.vars)) == 0:
            logger.info("Intersection of vars and projected is empty")
            return self.final_result(self.call_solver("sat"))

        #sharpsat limit
        #if len(self.formula.clauses) <= 3000:
        #if self.depth > 0 and ((len(self.projected) <= 64 and len(self.formula.clauses) <= 1500) or (len(self.projected) <= 32)):
        #    return self.final_result(self.solve_classic())
        if self.depth >= cfg["nesthdb"]["max_recursion_depth"]:
            return self.final_result(self.solve_classic())

        self.decompose_nested_primal()

        if interrupted:
            return -1

        if self.depth > 0 and self.graph.tree_decomp.tree_width >= cfg["nesthdb"]["threshold_hybrid"]: #TODO OR PROJECTION SIZE BELOW TRESHOLD OR CLAUSE SIZE BELOW TRESHOLD
            logger.info("Tree width >= hybrid threshold ({})".format(cfg["nesthdb"]["threshold_hybrid"]))
            return self.final_result(self.solve_classic())

        if self.graph.tree_decomp.tree_width >= cfg["nesthdb"]["threshold_abstract"]:
            logger.info("Tree width >= abstract threshold ({})".format(cfg["nesthdb"]["threshold_abstract"]))
            self.choose_subset()
            logger.info(f"Subset #non-nested: {len(self.non_nested)}")
            self.decompose_nested_primal()
            if self.graph.tree_decomp.tree_width >= cfg["nesthdb"]["threshold_abstract"]:
                logger.info("Tree width after abstraction >= abstract threshold ({})".format(cfg["nesthdb"]["threshold_abstract"]))
                return self.final_result(self.solve_classic())

        return self.final_result(self.nestedpmc())

    def solve_rec(self, vars, clauses, non_nested, projected, depth=0, **kwargs):
        if interrupted:
            return -1

        p = Problem(Formula(vars,clauses,projected),non_nested,depth, **kwargs)
        self.sub_problems.add(p)
        result = p.solve()
        self.sub_problems.remove(p)
        return result

    def interrupt(self):
        logger.warning("Problem interrupted")
        interrupted = True
        if self.nested_problem != None:
            self.nested_problem.interrupt()
        for p in list(self.sub_problems):
            p.interrupt()
        if self.active_process != None:
            if self.active_process.poll() is None:
                self.active_process.send_signal(signal.SIGTERM)

    def output_result(self, result):
        return f"PMC: {result}"

class ELPProblem(Problem):
    @classmethod
    def prepare_instance(cls, fname, args):
        elp = ELP.from_file(fname)
        if args.qr:
            # use comma-seperator reader and set the atoms in elp
            qsr = QuantitiveSelectionReader(elp)
            qsr.from_file(args.qr.name)
            elp = qsr.elp
        return cls(elp,elp.epistemic_atoms,**vars(args))

    def __init__(self, elp, non_nested, depth=0, **kwargs):
        self.elp = elp
        self.non_nested = elp.atoms
        self.non_nested_orig = non_nested
        self.depth = depth
        self.fallback_depth = depth
        self.kwargs = kwargs
        self.sub_problems = set()
        self.nested_problem = None
        self.active_process = None
        self.count = kwargs.get('count_solutions')
        self.qr = kwargs.get('qr')

    def preprocess(self):
        return

    def decompose_nested_primal(self):
        atoms, edges, adj = elp2primal(self.elp.atoms, self.elp.rules, self.elp.extra_atoms, self.elp.var_rule_dict, True)
        self.graph = Graph(self.elp.atoms, edges, adj)
        logger.info(f"Primal graph #vertices: {len(atoms)}, #edges: {len(edges)}")
        self.graph.abstract(self.non_nested)
        logger.info(f"Nested primal graph #vertices: {self.graph.num_nodes}, #edges: {self.graph.num_edges}")
        self.graph.decompose(**self.kwargs)

    def choose_subset(self):
        super().choose_subset()

    def call_solver(self, type):
        global cfg
        # logger.info(f"Call solver: {type} with #vars {self.formula.num_vars}, #clauses {len(self.formula.clauses)}, #projected {len(self.projected)}")

        cfg_str = f"{type}_solver"
        assert(cfg_str in cfg["nesthdb"])
        assert("path" in cfg["nesthdb"][cfg_str])
        local_cfg = cfg["nesthdb"][cfg_str]
        solver = [local_cfg["path"]]

        assert ("output_parser" in cfg["nesthdb"][cfg_str])

        if "args" in local_cfg:
            solver.extend(local_cfg["args"].split(' '))

        solver_parser = local_cfg["output_parser"]
        reader_module = importlib.import_module("dpdb.reader")
        solver_parser_cls = getattr(reader_module, solver_parser["class"])

        tmp = tempfile.NamedTemporaryFile().name
        with FileWriter(tmp) as fw:
            fw.write_elp(self.elp)
            if interrupted:
                return -1
            # self.active_process = psolver = subprocess.Popen(solver + [tmp], stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL)
            # output = solver_parser_cls.from_stream(psolver.stdout,**solver_parser["args"])
            # psolver.wait()
            # psolver.stdout.close()

            self.active_process = psolver = subprocess.Popen(solver + [tmp], stdin=subprocess.DEVNULL, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL)

            try:
                if self.fallback_depth < cfg["nesthdb"]["fallback_recursion_depth"]:
                    output, _ = psolver.communicate(timeout=cfg["nesthdb"]["max_solver_time"])
                else:
                    output, _ = psolver.communicate()
                psolver.stdout.close()
                output = solver_parser_cls.from_string(output.decode(), **solver_parser["args"])
            except subprocess.TimeoutExpired:
                logging.warning("Solver ran into timeout: fallback")
                self.fallback_depth = self.fallback_depth+1
                return self.solve(fallback=True)

            self.active_process = None
            if interrupted:
                return -1

            result = getattr(output, solver_parser["result"])

            if self.count or self.qr:
                try:
                    result = int(result) if result else 0
                except ValueError:
                    result = 1 if result == "SATISFIABLE" else 0
            else:
                result = True if result == "SATISFIABLE" else False


        logger.info(f"Solver {type} result: {result}")
        return result

    def solve_classic(self):
        if interrupted:
            return -1

        return self.call_solver("elp_count") if (self.count or self.qr) else self.call_solver("elp")

    def final_result(self,result):
        final = result
        if not self.kwargs["no_cache"]:
            rules = self.elp.rules + [self.elp.epistemic_constraints] + self.elp.choice_rules
            frozen_rules = freeze(rules)
            if result > 0:
                pos_cache[frozen_rules] = final
            else:
                neg_cache[frozen_rules] = final
            logger.info(f"Cache size: {len(pos_cache)} positive entries/{len(neg_cache)} negative entries")
        return final

    def get_cached(self):
        rules = self.elp.rules + [self.elp.epistemic_constraints] + self.elp.choice_rules
        frozen_rules = freeze(rules)

        if frozen_rules in pos_cache:
            return pos_cache[frozen_rules]
        else:
            if frozen_rules in neg_cache:
                return neg_cache[frozen_rules]
            # for negative instances a subset is sufficient
            for key in list(neg_cache):
                if key.issubset(frozen_rules):
                    return neg_cache[key]
        return None

    def nestedelp(self):
        global cfg

        pool = BlockingThreadedConnectionPool(1,cfg["db"]["max_connections"],**cfg["db"]["dsn"])
        problem_cfg = {}

        if "problem_specific" in cfg and "nestelp" in cfg["problem_specific"]:
            problem_cfg = cfg["problem_specific"]["nestelp"]
        if interrupted:
            return -1
        self.nested_problem = NestElp("NestedElp",pool, **cfg["dpdb"], **flatten_cfg(problem_cfg, [], '_',NestElp.keep_cfg()),**self.kwargs)
        if interrupted:
            return -1
        self.nested_problem.set_td(self.graph.tree_decomp)
        if interrupted:
            return -1
        self.nested_problem.set_recursive(self.solve_rec,self.depth)
        if interrupted:
            return -1
        self.nested_problem.set_input(self.graph.num_nodes,-1,self.non_nested_orig,self.elp)
        if interrupted:
            return -1
        self.nested_problem.setup()
        if interrupted:
            return -1
        self.nested_problem.solve()
        if interrupted:
            return -1
        if self.count:
            return self.nested_problem.model_count
        elif self.qr:
            if (self.nested_problem.model_count == 0):
                return 0
            return (self.nested_problem.projected_count/self.nested_problem.model_count)
        else:
            return self.nested_problem.sat


    def solve(self, fallback=False):
        self.preprocess()

        self.non_nested = self.non_nested.intersection(self.elp.epistemic_atoms)

        if not self.kwargs["no_cache"]:
            cached = self.get_cached()
            if cached != None:
                logger.info(f"Cache hit - Result: {cached}")
                return cached

        # no epistemic -> asp solve
        if len(self.elp.epistemic_atoms.intersection(self.elp.atoms)) == 0 and constraints_is_empty(self.elp.epistemic_constraints):
            logger.info("No epistemic atoms left")
            return self.final_result(self.call_solver("asp"))

        if len(self.elp.epistemic_atoms.intersection(self.elp.atoms)) == 0 and not constraints_is_empty(self.elp.epistemic_constraints):
            logger.info("No epistemic atoms left, epistemic constraints present")
            return self.final_result(self.solve_classic())

        # max recursion depth -> classic solve
        if self.depth >= cfg["nesthdb"]["max_recursion_depth"] and not fallback:
            logger.info("Maximal recursion depth")
            return self.final_result(self.solve_classic())

        self.decompose_nested_primal()

        if interrupted:
            return -1

        if self.depth > 0 and self.graph.tree_decomp.tree_width >= cfg["nesthdb"]["threshold_hybrid"] and not fallback:
            logger.info("Tree width >= hybrid threshold ({})".format(cfg["nesthdb"]["threshold_hybrid"]))
            return self.final_result(self.solve_classic())

        if self.graph.tree_decomp.tree_width >= cfg["nesthdb"]["threshold_abstract"]:
            logger.info("Tree width >= abstract threshold ({})".format(cfg["nesthdb"]["threshold_abstract"]))
            self.choose_subset()
            logger.info(f"Subset #non-nested: {len(self.non_nested)}")
            self.decompose_nested_primal()
            if self.graph.tree_decomp.tree_width >= cfg["nesthdb"]["threshold_abstract"]:
                logger.info("Tree width after abstraction >= abstract threshold ({})".format(cfg["nesthdb"]["threshold_abstract"]))
                return self.final_result(self.solve_classic())

        return self.final_result(self.nestedelp())

    def solve_rec(self, atoms, rules, choice_rules, extra_atoms, var_symbol_dict, non_nested, epistemic_atoms, qr_atoms, epistemic_constraints, depth=0, **kwargs):
        if interrupted:
            return -1
        p = ELPProblem(ELP(atoms, rules, choice_rules, extra_atoms, epistemic_atoms, qr_atoms, epistemic_constraints, var_symbol_dict), non_nested, depth, **kwargs)

        self.sub_problems.add(p)
        result = p.solve()
        self.sub_problems.remove(p)
        return result

    def interrupt(self):
        logger.warning("Problem interrupted")
        interrupted = True
        if self.nested_problem != None:
            self.nested_problem.interrupt()
        for p in list(self.sub_problems):
            p.interrupt()
        if self.active_process != None:
            if self.active_process.poll() is None:
                self.active_process.send_signal(signal.SIGTERM)

    def output_result(self, result):
        if self.count:
            return f"Problem has {result} world view(s)"
        if self.qr:
            return f"The probability of the selected combination is {result*100}%."
        else:
            return f"ELP: {'SATISFIABLE' if result else 'UNSATISFIABLE'}"

def read_input(fname):
    input = CnfReader.from_file(fname)
    return input.num_vars, input.vars, input.num_clauses, input.clauses, input.projected

CLASS_MAP = {NestElp: ELPProblem.prepare_instance,
                    NestPmc: Problem.prepare_instance}

def main():
    global cfg, args
    arg_parser = setup_arg_parser("%(prog)s [general options] -f input-file")
    arg_parser.add_argument("--no-cache", dest="no_cache", help="Disable cache", action="store_true")
    args = parse_args(arg_parser)
    cfg = read_cfg(args.config)
    fname = args.file

    prob = CLASS_MAP[vars(args)['cls']](fname, args)

    def signal_handler(sig, frame):
        if sig == signal.SIGUSR1:
            logger.warning("Terminating because of error in worker thread")
        else:
            logger.warning("Killing all connections")
        prob.interrupt()
        app_name = None
        if "application_name" in cfg["db"]["dsn"]:
            app_name = cfg["db"]["dsn"]["application_name"]
        admin_db.killall(app_name)

    admin_db = DBAdmin.from_cfg(cfg["db_admin"])
    signal.signal(signal.SIGINT, signal_handler)
    signal.signal(signal.SIGTERM, signal_handler)
    signal.signal(signal.SIGUSR1, signal_handler)

    result = prob.solve()
    logger.info(prob.output_result(result))

if __name__ == "__main__":
    main()

