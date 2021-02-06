# -*- coding: future_fstrings -*-
from dpdb.problem import *
from collections import defaultdict

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

def _path_between(i, j, edges):
    return False
    # if i < j:
    #     for
    # else:

def elp2primal (atoms_orig, rules, var_rule_dict = defaultdict(set), ret_adj=False):
    edges = set([])
    adj = {}

    for rule in rules:
        atoms = [abs(atom) for atom in rule['head']+rule['body']]
        rule_set = hashabledict({frozenset(atoms): hashabledict(rule)})
        for i in atoms:
            var_rule_dict[i].add(rule_set)
            for j in atoms:
                _add_directed_edge(edges,adj,i,j)
                _add_directed_edge(edges,adj,j,i)

    if ret_adj:
        return (atoms_orig, edges, adj)
    else:
        return (atoms_orig, edges)

def covered_rules(rules, vertices):
    vertice_set = set(vertices)
    cur_cl = set()
    for v in vertices:
        candidates = rules[v]
        for d in candidates:
            for key, val in d.items():
                if key.issubset(vertice_set):
                    cur_cl.add(val)

    return list(cur_cl)

def get_fact(atom, var_symbol_dict):
    if(atom > 0):
        return f"{var_symbol_dict[atom]}"
    else:
        if var_symbol_dict[abs(atom)].startswith('-'):
            return f"{var_symbol_dict[abs(atom)][1:]}"
        else:
            return f"-{var_symbol_dict[abs(atom)]}"

