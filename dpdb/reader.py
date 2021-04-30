import logging
import re
import sys
import lib.eclingo.eclingo.main as eclingo
from pprint import pprint
from collections import defaultdict

logger = logging.getLogger(__name__)


class Reader(object):
    def __init__(self, silent=False):
        self.silent = silent

    @classmethod
    def from_file(cls, fname, **kwargs):
        with open(fname, "r") as f:
            return cls.from_string(f.read(), **kwargs)

    @classmethod
    def from_stream(cls, stream, **kwargs):
        return cls.from_string(stream.read().decode(), **kwargs)

    @classmethod
    def from_string(cls, string, **kwargs):
        instance = cls(**kwargs)
        instance.parse(string)
        return instance

    def parse(self, string):
        pass


class RegExReader(Reader):
    def __init__(self, pattern, silent=False):
        super().__init__(silent)
        self.pattern = pattern
        self.result = None

    def parse(self, string):
        m = re.search(self.pattern, string)
        if m:
            self.result = m.group(1)
        else:
            self.result = 0
            # logger.error("Unable to parse input {0}".format(string))

class SciNumberRegExReader(RegExReader):
    def __init__(self, pattern, silent=False):
        super().__init__(pattern, silent)

    def parse(self, string):
        super().parse(string)
        if self.result is None:
            return
        dot = self.result.find(".")
        exp = self.result.find("e+")
        if dot >= 0 and exp >= 0:
            sdec = self.result[dot + 1:exp]
            self.result = int(self.result[0:dot] + sdec) * (10 ** (int(self.result[exp + 2:]) - len(sdec)))


class DimacsReader(Reader):
    def parse(self, string):
        self.string = string
        self.problem_solution_type = "?"
        self.format = "?"
        self.done = False
        lines = string.split("\n")
        body_start = self.preamble(lines)
        self.store_problem_vars()
        if not self.done:
            self.body(lines[body_start:])

    def store_problem_vars(self):
        pass

    def is_comment(self, line):
        return line.startswith("c ") or line == "c"

    def body(self, string):
        pass

    def preamble_special(self, line):
        return False

    def preamble(self, lines):
        for lineno, line in enumerate(lines):
            if line.startswith("p ") or line.startswith("s "):
                line = line.split()
                self.problem_solution_type = line[0]
                self.format = line[1]
                self._problem_vars = line[2:]
                return lineno + 1
            elif not line or self.is_comment(line):
                continue
            else:
                if self.preamble_special(line):
                    return lineno + 1
                else:
                    logger.warning("Invalid content in preamble at line %d: %s", lineno, line)
        logger.error("No type found in DIMACS file!")
        sys.exit(1)


class CnfReader(DimacsReader):
    def __init__(self, silent=False):
        super().__init__(silent)
        self.vars = set()
        self.clauses = []
        self.solution = -1
        self.projected = set()
        self.maybe_sat = True
        self.models = None
        self.error = False
        # self.single_clauses_only = set()
        self.single_clauses = set()
        self.single_vars = set()

    def parse(self, string):
        super().parse(string)

    def is_comment(self, line):
        if line.startswith("c ind "):
            projected, lines = self.read_terminated(None, line[6:], 0)
            [self.projected.add(p) for p in projected]
            return False
        elif line == 'c UNSATISFIABLE':
            return False
        else:
            return super().is_comment(line)

    def preamble_special(self, line):
        if line == 'c UNSATISFIABLE':
            self.maybe_sat = False
            return True
        return False

    def store_problem_vars(self):
        # We assume a CNF file containing a solution is pre-solved by pmc and
        # the solution line contains only the number of models for sharpsat
        if self.problem_solution_type == 's':
            try:
                self.models = int(self.format)
            except ValueError:
                if self.format == "UNSATISFIABLE":
                    self.models = 0
                    self.maybe_sat = False
                elif self.format == "SATISFIABLE":
                    self.models = 1
                elif self.format == "inf":
                    self.error = True
                else:
                    logger.warning("Unable to parse solution %s", self.string)
            if not self.silent:
                logger.info("Problem has %d models (solved by pre-processing)", int(self.models))
            self.done = True
            self.num_vars = 0
            self.num_clauses = 0
        elif not self.maybe_sat:
            self.models = 0
            if not self.silent:
                logger.info("Problem has 0 models (solved by pre-processing)")
            self.done = True
            self.num_vars = 0
            self.num_clauses = 0
        else:
            self.num_vars = int(self._problem_vars[0])
            self.num_clauses = int(self._problem_vars[1])

    def read_terminated(self, lines, line, lineno):
        i = 1
        while line[-1] != '0':
            if lineno + i >= len(lines):
                logger.warning("Clause at line %d not terminated with 0", lineno)
                # Ignore clause instead of "fixing" it?
                line += " 0"
                break
            line += lines[lineno + i]
            lines[lineno + i] = None
            i += 1
        content = [int(v) for v in line.split()[:-1]]

        return (content, lines)

    def body(self, lines):
        if self.format != "cnf":
            logger.error("Not a cnf file!")
            sys.exit(1)

        maxvar = 0
        # projected_vars = set()

        for lineno, line in enumerate(lines):
            if not line or self.is_comment(line):
                continue
            elif line.startswith("pv "):
                projected, lines = self.read_terminated(lines, line[3:], lineno)
                [self.projected.add(p) for p in projected]
            elif line.startswith("c ind "):
                projected, lines = self.read_terminated(lines, line[6:], lineno)
                [self.projected.add(p) for p in projected]
            elif line.startswith("a "):
                projected, lines = self.read_terminated(lines, line[2:], lineno)
                [self.projected.add(p) for p in projected]
            elif line.startswith("e "):
                continue
            else:
                clause, lines = self.read_terminated(lines, line, lineno)
                if len(clause) == 1:
                    if -clause[0] in self.single_clauses:  # UNSAT
                        self.maybe_sat = False
                        self.models = 0
                        break
                    self.single_clauses.add(clause[0])
                else:
                    self.clauses.append(clause)

        # simplify with single clauses, avoid copies, do it at most 10 times in a row
        iterate = 0
        removed_singles = True
        while iterate < 10 and removed_singles:
            removed_singles = False
            i = 0
            while i < len(self.clauses):
                j = 0
                cl = self.clauses[i]
                while j < len(cl):
                    if cl[j] in self.single_clauses:  # clause sat, not needed anymore
                        del self.clauses[i]  # remove clause
                        i = i - 1
                        break
                    elif -cl[j] in self.single_clauses:  # remove false literal
                        del cl[j]
                        j = j - 1
                        if len(cl) == 1:  # newly turned single!
                            removed_singles = True
                            self.single_clauses.add(cl[j])
                            del self.clauses[i]  # remove clause
                            i = i - 1
                            if -cl[j] in self.single_clauses:  # UNSAT
                                self.maybe_sat = False
                                self.models = 0
                                i = len(self.clauses)
                            break
                    j = j + 1
                i = i + 1
        iterate = iterate + 1

        for clause in self.clauses:
            self.vars.update([abs(lit) for lit in clause])
        maxvar = max(maxvar, max(self.vars))

        self.single_vars = set((abs(l) for l in self.single_clauses))
        self.projected = self.projected.difference(self.single_vars)

        # maxvar = max(maxvar,max(self.projected))
        # self.projected = projected_vars
        if maxvar != self.num_vars:
            logger.warning("Effective number of variables mismatch preamble (%d vs %d)", maxvar, self.num_vars)
        if len(self.clauses) != self.num_clauses:
            logger.warning("Effective number of clauses mismatch preamble (%d vs %d)", len(self.clauses),
                           self.num_clauses)


def _add_directed_edge(edges, adjacency_list, vertex1, vertex2):
    if vertex1 in adjacency_list:
        adjacency_list[vertex1].append(vertex2)
    else:
        adjacency_list[vertex1] = [vertex2]
    edges.append((vertex1, vertex2))


class TdReader(DimacsReader):
    def __init__(self, silent=False):
        super().__init__(silent)
        self.edges = []
        self.bags = {}
        self.adjacency_list = {}

    def store_problem_vars(self):
        if self.problem_solution_type == "p":
            self.num_vertices = int(self._problem_vars[0])
            self.num_edges = int(self._problem_vars[1])
        elif self.problem_solution_type == "s":
            self.num_bags = int(self._problem_vars[0])
            self.tree_width = int(self._problem_vars[1]) - 1
            self.num_orig_vertices = int(self._problem_vars[2])
        else:
            logger.error("Unrecognized problem or solution indicator: %s", self.problem_solution_type)

    def _add_directed_edge(self, vertex1, vertex2):
        if vertex1 in self.adjacency_list:
            self.adjacency_list[vertex1].append(vertex2)
        else:
            self.adjacency_list[vertex1] = [vertex2]
        self.edges.append((vertex1, vertex2))

    def body(self, lines):
        if self.format != "td":
            logger.error("Not a td file!")
            sys.exit(1)

        for lineno, line in enumerate(lines):
            if not line:
                continue

            if self.is_comment(line):
                line = line.split()
                if len(line) > 2 and line[1] == 'r':
                    self.root = int(line[2])
            elif line.startswith("b "):
                line = line.split()
                self.bags[int(line[1])] = [int(v) for v in line[2:]]
            else:
                line = line.split()
                if len(line) != 2:
                    logger.warning("Expected exactly 2 vertices at line %d, but %d found", lineno, len(line))
                vertex1 = int(line[0])
                vertex2 = int(line[1])

                _add_directed_edge(self.edges, self.adjacency_list, vertex1, vertex2)
                _add_directed_edge(self.edges, self.adjacency_list, vertex2, vertex1)

        if self.problem_solution_type == "p":
            if len(self.edges) != self.num_edges * 2:
                logger.warning("Effective number of edges mismatch preamble (%d vs %d)", len(self.edges) / 2,
                               self.num_edges)
        elif self.problem_solution_type == "s":
            if len(self.bags) != self.num_bags:
                logger.warning("Effective number of bags mismatch preamble (%d vs %d)", len(self.bags), self.num_bags)


class TwReader(DimacsReader):
    def __init__(self, silent=False):
        super().__init__(silent)
        self.edges = []
        self.adjacency_list = {}

    def store_problem_vars(self):
        self.num_vertices = int(self._problem_vars[0])
        self.num_edges = int(self._problem_vars[1])

    def body(self, lines):
        if self.format != "tw":
            logger.error("Not a tw file!")
            sys.exit(1)

        for lineno, line in enumerate(lines):
            if not line or self.is_comment(line):
                continue

            line = line.split()
            if len(line) != 2:
                logger.warning("Expected exactly 2 vertices at line %d, but %d found", lineno, len(line))
            vertex1 = int(line[0])
            vertex2 = int(line[1])

            _add_directed_edge(self.edges, self.adjacency_list, vertex1, vertex2)
            _add_directed_edge(self.edges, self.adjacency_list, vertex2, vertex1)

        if len(self.edges) != self.num_edges * 2:
            logger.warning("Effective number of edges mismatch preamble (%d vs %d)", len(self.edges) / 2,
                           self.num_edges)


class EdgeReader(DimacsReader):
    def __init__(self, silent=False):
        super().__init__(silent)
        self.edges = []
        self.adjacency_list = {}

    def store_problem_vars(self):
        self.num_vertices = int(self._problem_vars[0])
        self.num_edges = int(self._problem_vars[1])

    def body(self, lines):
        if self.format != "edge":
            logger.error("Not a edge file!")
            sys.exit(1)

        for lineno, line in enumerate(lines):
            if not line or self.is_comment(line):
                continue

            line = line.split()
            if line[0] != 'e':
                logger.warning("Invalid line %d", lineno)
            vertex1 = int(line[1])
            vertex2 = int(line[2])

            _add_directed_edge(self.edges, self.adjacency_list, vertex1, vertex2)
            _add_directed_edge(self.edges, self.adjacency_list, vertex2, vertex1)

        if len(self.edges) != self.num_edges * 2:
            logger.warning("Effective number of edges mismatch preamble (%d vs %d)", len(self.edges) / 2,
                           self.num_edges)


class QuantitiveSelectionReader():
    def __init__(self, elp, silent=False):
        self.elp = elp
        self.qr_atoms = set()

    def from_file(self, fname, **kwargs):
        with open(fname, "r") as f:
            self.from_string(f.read(), **kwargs)

    def from_stream(self, stream, **kwargs):
        self.from_string(stream.read.decode(), **kwargs)

    def from_string(self, string, **kwargs):
        self.parse(string)

    def parse(self, string):
        for symbol in string.split():
            _factor = 1
            if symbol.startswith('-'):
                symbol = symbol[1:]
                _factor = -1
            print (symbol)
            atom = None
            # get atom-nr by symbol
            print (self.elp.var_symbol_dict)
            for a, s in self.elp.var_symbol_dict.items():
                if s == symbol:
                    atom = a

            # check for aux atoms
            # check if found
            if (atom is None):
                for a, s in self.elp.var_symbol_dict.items():
                    if s == f"aux_{symbol}" or\
                            s == f"aux_not_{symbol}" or\
                            s == f"aux_sn_{symbol}" or\
                            s == f"aux_not_sn_{symbol}":
                        atom = a
                if (atom is None):
                    logger.error(f"Atom {symbol} not found in ELP")
                    sys.exit(1)
            # check if in epistemic list
            if (atom not in self.elp.epistemic_atoms):
                logger.error(f"Atom {symbol} is not epistemic")
                sys.exit(1)

            # add to qr_atoms
            self.elp.qr_atoms.add(atom*_factor)


class ELPReader(Reader):
    def __init__(self):
        self.atoms = set()
        self.epistemic_atoms = set()
        self.epistemic_not_atoms = set()
        self.rules = []
        self.facts = set()
        self.choice_rules = []
        self.var_symbol_dict = {}
        self.symbol_var_dict = {}
        self.extra_atoms = {}

        self.clingo_rules = []
        self.clingo_facts = []
        self.clingo_choice_rules = []
        self.epistemic_symbols = []

    def parse(self, string):
        eclingo_control = eclingo.Control(optimization=0)
        eclingo_control.add(string)
        eclingo_control.parse()

        _external = "_atom_to_be_released"
        _aux = "aux_"
        _not = "not_"
        _sn = "sn_"
        _external_atom = -1

        # print grounded program
        # print("------------------------------------------------------------")
        # print("   Grounded Program")
        # print("------------------------------------------------------------")
        # pprint(eclingo_control.ground_program.objects)
        # print(eclingo_control.ground_program)

        for o in eclingo_control.ground_program.objects:
            # Rules
            if isinstance(o, eclingo.ClingoRule):
                if (o.body == [] and len(o.head) == 1):
                    if not (o.choice):
                        self.clingo_facts.append(o)
                    else:
                        self.choice_rules.append(o)
                else:
                    self.clingo_rules.append(o)
            # OutputAtoms
            elif isinstance(o, eclingo.ClingoOutputAtom):
                # remove _atom_to_be_released from atoms
                if (str(o.symbol) == _external):
                    _external_atom = o.atom
                    continue
                if (o.atom != 0):
                    self.var_symbol_dict[o.atom] = str(o.symbol)
                    self.symbol_var_dict[str(o.symbol)] = o.atom
                    self.atoms.add(o.atom)
                else:
                    self.facts.add(o.symbol)


        # add unmatched atoms
        for r in self.clingo_rules:
            for a in r.head + r.body:
                self.atoms.add(abs(a))

        for key, value in eclingo_control._epistemic_atoms.items():
            if (str(value) in self.symbol_var_dict.keys()):
                # if there is already one epistemic, note that to partners
                if self.symbol_var_dict[str(value)] in self.epistemic_atoms:
                    self.extra_atoms[self.symbol_var_dict[str(value)]].append(self.symbol_var_dict[str(key)])
                else:
                    self.epistemic_atoms.add(self.symbol_var_dict[str(value)])
                    self.extra_atoms[self.symbol_var_dict[str(value)]] = [self.symbol_var_dict[str(key)]]
                self.atoms.remove(self.symbol_var_dict[str(key)])
            else:
                self.epistemic_atoms.add(self.symbol_var_dict[str(key)])

        # remove auxilary-related rules which were added by eclingo
        # filter 1: check for choice-rules - e.g. { aux_eligible(mike) }.
        # filter 2: check for #external in rule body - e.g. aux_eligible(mike) :- _atom_to_be_released, eligible(mike).
        self.clingo_rules = [item for item in self.clingo_rules
                             if not (item.choice or  # filter 1
                                     _external_atom in item.body)] # or  # filter 2

        # save choice rules for not-auxilaries
        self.choice_rules = [item for item in self.choice_rules if not self.var_symbol_dict[item.head[0]].startswith("aux_")]
        self.choice_rules = [{'head': [v for v in cr.head], 'body': []} for cr in self.choice_rules]

        self.rules = [{'head': [v for v in cr.head], 'body': [v for v in cr.body]} for cr in self.clingo_rules]

        # add facts
        facts = []
        for f in self.facts:
            f = str(f)
            if f in self.symbol_var_dict.keys():
                facts.append({'head': [self.symbol_var_dict[f]], 'body': []})
            else:
                if f"aux_not_sn_{f[1:]}" in self.symbol_var_dict.keys():
                    facts.append({'head': [self.symbol_var_dict[f"aux_not_sn_{f[1:]}"]], 'body': []})
                elif f"aux_sn_{f[1:]}" in self.symbol_var_dict.keys():
                    facts.append({'head': [self.symbol_var_dict[f"aux_sn_{f[1:]}"]], 'body': []})
                elif f"aux_not_{f}" in self.symbol_var_dict.keys():
                    facts.append({'head': [self.symbol_var_dict[f"aux_not_{f}"]], 'body': []})
                elif f"aux_{f}" in self.symbol_var_dict.keys():
                    facts.append({'head': [self.symbol_var_dict[f"aux_{f}"]], 'body': []})

        self.rules = self.rules + facts

        # pprint(self.rules)
        # print (self.choice_rules)
        # pprint(self.var_symbol_dict)
        # print(self.atoms)
        # print(self.facts)
        # print(self.epistemic_atoms)
        # print(self.epistemic_not_atoms)
        # print(self.extra_atoms)