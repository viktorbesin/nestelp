# -*- coding: future_fstrings -*-
from dpdb.problem import *
from collections import defaultdict
import itertools

class hashabledict(dict):
    def __hash__(self):
        return hash(frozenset(self))

def freeze(d):
    if isinstance(d, dict):
        return frozenset((key, freeze(value)) for key, value in d.items())
    elif isinstance(d, list):
        return frozenset(freeze(value) for value in d)
    return d

def _add_directed_edge(edges, adjacency_list, vertex1, vertex2):
    if vertex1 == vertex2:
        return

    if vertex1 in adjacency_list:
        adjacency_list[vertex1].add(vertex2)
    else:
        adjacency_list[vertex1] = set([vertex2])
    if vertex1 < vertex2:
        edges.add((vertex1,vertex2))

def elp2primal (atoms_orig, rules, extra_atoms, var_rule_dict = defaultdict(set), ret_adj=False):
    edges = set([])
    adj = {}

    for rule in rules:
        atoms = [abs(atom) for atom in rule['head']+rule['body']]
        rule_set = hashabledict({frozenset(atoms): hashabledict(rule)})
        for i in atoms:
            if i not in atoms_orig:
                i = _get_main_atom(extra_atoms,i)
            var_rule_dict[i].add(rule_set)
            for j in atoms:
                if j not in atoms_orig:
                    j = _get_main_atom(extra_atoms,j)
                _add_directed_edge(edges,adj,i,j)
                _add_directed_edge(edges,adj,j,i)

    if ret_adj:
        return (atoms_orig, edges, adj)
    else:
        return (atoms_orig, edges)

def covered_rules(rules, vertices, extra_atoms):
    vertice_set = set(vertices)
    cur_cl = set()
    for v in vertices:
        candidates = rules[v]
        for d in candidates:
            for key, val in d.items():
                if key.issubset(vertice_set):
                    cur_cl.add(val)

    cur_cl.update(covered_extra_rules(rules, vertices, extra_atoms))
    return list(cur_cl)

def covered_extra_rules(rules, vertices, extra_atoms):
    vertice_set = set(vertices)
    for v in vertices:
        if v in extra_atoms.keys():
            vertice_set.update(set(extra_atoms[v]))

    cur_cl = set()
    for v in vertices:
        candidates = rules[v]
        for d in candidates:
            for key, val in d.items():
                if key.issubset(vertice_set):
                    cur_cl.add(val)

    return cur_cl

def get_subjective_reduct(rules, var_symbol_dict, extra_atoms, n, v):
    reduct = []

    atoms = [n] + extra_atoms[n] if n in extra_atoms.keys() else [n]
    atoms = [n for n in atoms if var_symbol_dict[n].startswith("aux_")]

    for r in rules:
        app = r
        for atom in atoms:
            _v = v
            _not = True if var_symbol_dict[atom].startswith("aux_not") else False
            if _not:
                _v = False if v else True

            if atom in r['body']:
                # remove it from body -> True
                if _v:
                    app = {'head': app['head'], 'body': [b for b in app['body'] if not b in atoms]}
                # remove the rule -> False
                else:
                    app = None
                    break
            elif (-1) * atom in r['body']:
                # remove the rule -> not True
                if _v:
                    app = None
                    break
                # remove it from body -> not False
                else:
                    app = {'head': app['head'], 'body': [b for b in app['body'] if not b == (-1) * atom]}
        if app == None:
            continue
        else:
            reduct.append(app)

    return reduct


def get_epistemic_constraints(epistemic_constraints, pn_constraint, undecided_constraints):
    ec = epistemic_constraints.copy()
    if pn_constraint is not None:
        for ba in pn_constraint['body']:
            if ba < 0:
                ec['n'].append(ba)
            else:
                ec['p'].append(ba)
    for ua in undecided_constraints:
        ec['u'].append(abs(ua[0]['body'][0]))

    return ec

def get_relevant_constraints(epistemic_constraints, atoms, extra_atoms):
    ec = {'p': [], 'n': [], 'u': []}
    for p in epistemic_constraints['p']:
        if p in atoms or _get_main_atom(extra_atoms, p) in atoms:
            ec['p'].append(p)
    for n in epistemic_constraints['n']:
        if n in atoms or _get_main_atom(extra_atoms, n) in atoms:
            ec['n'].append(n)
    for u in epistemic_constraints['u']:
        if u in atoms or _get_main_atom(extra_atoms, u) in atoms:
            ec['u'].append(u)
    return ec

def constraints_is_empty(epistemic_constraints):
    return len(epistemic_constraints['p']) == 0 and len(epistemic_constraints['n']) == 0 and len(epistemic_constraints['u']) == 0

def _get_main_atom(extra_atoms, atom):
    keys = list(extra_atoms.keys())
    vals = list(extra_atoms.values())

    for val in vals:
        if atom in val:
            return keys[vals.index(val)]
    return -1

def write_current_elp(rules, choice_rules, epistemic_atoms, epistemic_constraints, var_symbol_dict):
    def _get_symbol_for_atom(atom, head=False):
        if abs(atom) not in var_symbol_dict.keys():
            return f"x_{abs(atom)}" if atom > 0 else f"not x_{abs(atom)}"
        if atom < 0:
            _neg = "not"
        else:
            _neg = ""
        symbol = var_symbol_dict[abs(atom)]

        # check if its still epistemic
        if symbol.startswith("aux_not_sn_"):
            if head:
                return f"-{symbol[11:]}"
            return f"{_neg} &k{{~ -{symbol[11:]}}}" if len(epistemic_atoms) > 0 else f"{_neg} -{symbol[11:]}"
        elif symbol.startswith("aux_sn_"):
            if head:
                return f"-{symbol[7:]}"
            return f"{_neg} &k{{-{symbol[7:]}}}" if len(epistemic_atoms) > 0 else f"{_neg} -{symbol[7:]}"
        elif symbol.startswith("aux_not_"):
            if head:
                return f"{symbol[8:]}"
            return f"{_neg} &k{{~ {symbol[8:]}}}" if len(epistemic_atoms) > 0 else f"{_neg} {symbol[8:]}"
        elif symbol.startswith("aux_"):
            if head:
                return f"{symbol[4:]}"
            return f"{_neg} &k{{{symbol[4:]}}}" if len(epistemic_atoms) > 0 else f"{_neg} {symbol[4:]}"

        return f"{_neg} {symbol}"

    str_rules = []

    for cr in choice_rules:
        str_rules.append(f"{{ {_get_symbol_for_atom(cr['head'][0])} }}.")

    for r in rules:
        if (r['body'] == []):
            if (len(r['head']) == 0):
                str_rules.append(f":- .")
                continue
            if (len(r['head']) == 1):
                str_rules.append(f"{_get_symbol_for_atom(r['head'][0], True)}.")
                continue
            str_rules.append(f"{','.join([_get_symbol_for_atom(ha, True) for ha in r['head']])}.")
        else:
            str_rules.append(f"{','.join([_get_symbol_for_atom(ha, True) for ha in r['head']])} :- "
                   f"{','.join([_get_symbol_for_atom(ba) for ba in r['body']])}.")

    for pc in epistemic_constraints['p']:
        str_rules.append(f":- not &k{{{_get_symbol_for_atom(abs(pc), True)}}}.")
    for nc in epistemic_constraints['n']:
        str_rules.append(f":- not &k{{~{_get_symbol_for_atom(abs(nc), True)}}}.")
    for uc in epistemic_constraints['u']:
        symbol = _get_symbol_for_atom(abs(uc), True)
        str_rules.append(f":- &k{{{symbol}}}.")
        str_rules.append(f":- &k{{~{symbol}}}.")

    print ('\n'.join(str_rules))

