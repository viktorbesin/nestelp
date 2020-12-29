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

def elp2primal (atoms_orig, rules, atom_rule_dict = defaultdict(set), ret_adj=False):
    edges = set([])
    adj = {}

    for rule in rules:
        # TODO: abs() needed? what about ~a(X)?
        atoms = [abs(atom) for atom in rule.head+rule.body]
        rule_set = hashabledict({frozenset(atoms): frozenset(rule.head+rule.body)})
        for i in atoms:
            atom_rule_dict[i].add(rule_set)
            for j in atoms:
                _add_directed_edge(edges,adj,i,j)
                _add_directed_edge(edges,adj,j,i)

    if ret_adj:
        return (atoms_orig, edges, adj)
    else:
        return (atoms_orig, edges)

