# -*- coding: future_fstrings -*-
from dpdb.problem import *
from collections import defaultdict
import itertools

class hashabledict(dict):
    def __hash__(self):
        return hash(frozenset(self))

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
    for atom in [n] + extra_atoms[n] if n in extra_atoms.keys() else [n]:
        symbol = var_symbol_dict[atom]
        if symbol.startswith("aux_"):

            for r in rules:
                if atom in r['body']:
                    # remove it from body -> True
                    if v:
                        reduct.append({'head': r['head'], 'body': [b for b in r['body'] if not b == atom]})
                    # remove the rule -> False
                    else:
                        continue
                elif (-1)*atom in r['body']:
                    # remove the rule -> not True
                    if v:
                        continue
                    # remove it from body -> not False
                    else:
                        reduct.append({'head': r['head'], 'body': [b for b in r['body'] if not b == (-1)*atom]})
                else:
                    reduct.append(r)

    return reduct


def _get_main_atom(extra_atoms, atom):
    keys = list(extra_atoms.keys())
    vals = list(extra_atoms.values())

    for val in vals:
        if atom in val:
            return keys[vals.index(val)]
    return -1

def get_fact(atom, var_symbol_dict):
    if(atom > 0):
        return f"{var_symbol_dict[atom]}"
    else:
        if var_symbol_dict[abs(atom)].startswith('-'):
            return f"{var_symbol_dict[abs(atom)][1:]}"
        else:
            return f"-{var_symbol_dict[abs(atom)]}"

