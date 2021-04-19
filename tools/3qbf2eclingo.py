#!/usr/bin/env python3

from lark import Lark
from lark import Transformer
import collections
import itertools
import sys
import argparse

argumentParser = argparse.ArgumentParser(description='Pseudo-reduces an e,3-QBF in QDIMACS-CNF format into ground &k{}/eclingo. Implements the hardness proof of Theorem 5 in (Shen, Eiter 2016). "Pseudo-reduces" because the reduction only works correctly for QBFs satisfying the restriction of the hardness proof, that is, the CNF has to evaluate to true if all Y variables are set to true. With an optional flag, the reduction can be modified to work correctly for all QBFs.')
argumentParser.add_argument('-i', metavar='FILE', type=argparse.FileType('r'), default=sys.stdin, help='QDIMACS input file (default standard input)')
argumentParser.add_argument('-o', metavar='FILE', type=argparse.FileType('w'), default=sys.stdout, help='&k{} output file (default standard output)')
argumentParser.add_argument('-c', '--correct-reduction', action='store_true', help='Use a reduction for all e,3-QBFs; also those which do not satisfy the restriction of the hardness proof. The default reduction only works for QBFs satisfying the restriction and may, when being used on QBFs not satisfying the restriction, produce an ELP whose world view existence is not equivalent to the QBF\'s validity. The correct reduction is bigger by a linear factor than the default one. (it introduces one new variable per clause.)')
args = argumentParser.parse_args()

# transformer that transforms the parsed syntax tree into a pair (Q, M), where Q ("binder") is a deque of pairs (q, l), where q ("quantifier") is either 'e' or 'a' and l is a deque of positive numbers, and M is an iterable of clauses, where a clause is an iterable of numbers.
class QdimacsSyntaxTreeTransformer(Transformer):
  def pnum(self, children):
    return int(children[0].value)
  def posnum(self, children):
    return children[0]
  def negnum(self, children):
    return -children[0]
  def quant_set(self, children):
    return children[0].value, collections.deque(children[1:-1])
  def prefix(self, children): # ensure consecutive binders have different quantifiers, otherwise combine them
    binder = collections.deque()
    for (q,l) in children:
      if not binder or binder[-1][0] != q:
        binder.append((q,l))
      else: #previous quantifier was equal; append to previous
        binder[-1][1].extend(l)
    return binder
  def clause(self, children):
    return children[:-1]
  def matrix(self, children):
    return children
  def program(self, children):
    return children[1], children[2]

# QDIMACS grammar parser:
qdimacsParser = Lark(r'''
  program: preamble prefix matrix
  preamble: COMMENT_LINE* problem_line
  problem_line: "p" "cnf" pnum pnum NEWLINE
  prefix: quant_set*
  quant_set: QUANTIFIER pnum+ "0" NEWLINE
  QUANTIFIER: "e"
            | "a"
  matrix: clause+
  clause: num+ "0" NEWLINE
  pnum: INT
  num: pnum     -> posnum
     | "-" pnum -> negnum

  COMMENT_LINE: "c" NEWLINE | "c" WS_INLINE NEWLINE | "c" WS_INLINE /[^\n]/* NEWLINE
      
  %import common.INT
  %import common.WS_INLINE
  %import common.NEWLINE
  %ignore WS_INLINE
  
  ''', start='program', parser='lalr', transformer=QdimacsSyntaxTreeTransformer())

qbf = qdimacsParser.parse(args.i.read())
if len(qbf[0]) != 3:
  print('ERROR: ' + str(len(qbf[0])) + ' quantifier alternations instead of 3', file=sys.stderr)
  sys.exit(1)
if qbf[0][0][0] != 'e':
  print('ERROR: first quantifier must be \'e\'', file=sys.stderr)
  sys.exit(1)

maxvar=0 # keeps track of highest variable so far

# in order to keep variable order of matrix, start with matrix:
clausenum=0 # keeps track of # of clauses
auxvar=None

# for each clause: u :- l_{i,1}*, l_{i,2}*, _{i,3}* | * function s.t. positive aux = naux, negative -aux = aux
for c in qbf[1]: # clause c is an iterable of signed numbers
  if args.correct_reduction:
    auxvar='naux' + str(clausenum)
  print('u :- ' + ', '.join(map(lambda n : 'na'+str(n) if n>0 else 'a'+str(-n), c)) + (', '+auxvar if auxvar else '') + '.', file=args.o)
  maxvar = max(itertools.chain([maxvar],map(lambda n : n if n>0 else -n, c)))
  clausenum+=1
# for each variable aux \in X: aux :- not &k{naux}. naux :- not &k{aux}.
for a in qbf[0][0][1]:
  maxvar = max(maxvar, a)
  var = 'a' + str(a)
  negvar = 'n' + var
  print(var + ' :- not &k{' + negvar + '}.', file=args.o)
  print(negvar + ' :- not &k{' + var + '}.', file=args.o)
# for each variable aux \in Y: aux :- not naux. naux :- not aux.
for a in qbf[0][1][1]:
  maxvar = max(maxvar, a)
  var = 'a' + str(a)
  negvar = 'n' + var
  print(var + ' :- not ' + negvar + '.', file=args.o)
  print(negvar + ' :- not ' + var + '.', file=args.o)
if args.correct_reduction: #also guess auxiliary Y variables
  for i in range(len(qbf[1])):
    var = 'aux' + str(i)
    negvar = 'n' + var
    print(var + ' :- not ' + negvar + '.', file=args.o)
    print(negvar + ' :- not ' + var + '.', file=args.o)
for a in qbf[0][2][1]:
  maxvar = max(maxvar, a)
  var = 'a' + str(a)
  negvar = 'n' + var
  print(var + ', ' + negvar + '.', file=args.o)
  print(var + ' :- u.', file=args.o)
  print(negvar + ' :- u.', file=args.o)
print('v :- not &k{v}, not &k{~u}.', file=args.o)

if args.i:
  args.i.close()
if args.o:
  args.o.close()

