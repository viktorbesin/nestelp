#!/usr/bin/env python3

from lark import Lark
from lark import Transformer
import collections
import itertools
import sys
import argparse

properties = {
  0: "highGPA({0}), fairGPA({0}).",
  1: "highGPA({0}), fairGPA({0}). minority({0}).",
  2: "highGPA({0}).",
  3: "fairGPA({0}). minority({0}).",
  4: "fairGPA({0}).",
  5: "minority({0}), highGPA({0}).",
  6: "fairGPA({0}), highGPA({0}). minority({0}).",
  7: "highGPA({0}).",
  8: "-highGPA({0}). -fairGPA({0}), minority({0}).",
  9: "-highGPA({0}). -fairGPA({0}). minority({0}).",
  10: "fairGPA({0}), highGPA({0}). minority({0}).",
  11: "fairGPA({0}). minority({0}).",
  12: "highGPA({0}).",
  13: "fairGPA({0}). -minority({0}).",
  14: "minority({0}).",
  15: "-highGPA({0}). fairGPA({0}), -fairGPA({0}). minority({0}).",
  16: "fairGPA({0}), highGPA({0}).",
  17: "highGPA({0}).",
  18: "-highGPA({0}). fairGPA({0}), -fairGPA({0}). minority({0}).",
  19: "",
  20: "highGPA({0}).",
  21: "fairGPA({0}), highGPA({0}). minority({0}).",
  22: "fairGPA({0}). minority({0}).",
  23: "fairGPA({0}). -minority({0}).",
  24: "-highGPA({0}). fairGPA({0}), -fairGPA({0}). minority({0})."
}

selection = {
  0: "lowChance({0})",
  1: "",
  2: "",
  3: "",
  4: "lowChance({0})",
  5: "",
  6: "",
  7: "",
  8: "",
  9: "-eligible({0})",
  10: "",
  11: "",
  12: "",
  13: "",
  14: "highChance({0})",
  15: "",
  16: "",
  17: "",
  18: "",
  19: "highChance({0})",
  20: "",
  21: "",
  22: "",
  23: "",
  24: "highChance({0})"
}

def check_positive(value):
  ivalue = int(value)
  if ivalue <= 0:
    raise argparse.ArgumentTypeError("%s is an invalid positive int value" % value)
  return ivalue

argumentParser = argparse.ArgumentParser(description='Generates eligible instances based on the number of students.')
argumentParser.add_argument('n', type=check_positive, help='Number of students')
argumentParser.add_argument('-o', metavar='FILE', type=argparse.FileType('w'), default=sys.stdout, help='output file (default standard output)')
argumentParser.add_argument('-qr', metavar='FILE', type=argparse.FileType('w'), help='output file for qr selection (only for extended eligible problem)')
argumentParser.add_argument('-e', '--extended', action='store_true', help='Use extended setting to enable more world views.')
args = argumentParser.parse_args()

print("eligible(X) :- highGPA(X), student(X).", file=args.o)
print("eligible(X) :- minority(X), fairGPA(X), student(X).", file=args.o)
print("-eligible(X) :- -fairGPA(X), -highGPA(X), student(X).", file=args.o)
print("interview(X) :- not &k{ eligible(X) }, not &k{ -eligible(X) }, student(X).", file=args.o)

if args.extended:
  print("lowChance(X) :- not &k{highChance(X)}, not &k{eligible(X)}, student(X).", file=args.o)
  print("highChance(X) :- not &k{lowChance(X)}, not &k{eligible(X)}, student(X).", file=args.o)
  if args.qr:
    qr = ""
    for i in range(0, int(args.n)):
      if i < 25:
        if selection.get(i) != "":
          qr += f" {selection.get(i).format(f's{i + 1}')}"
    print(qr, file=args.qr)

for i in range(0, int(args.n)):
  print(properties.get(i % 25).format(f"s{i+1}"), file=args.o)

for i in range(0, int(args.n)):
  print(f"student(s{i+1}).", file=args.o)

