import sys
import argparse
import pprint
import pysmt.operators as op
from pysmt.smtlib.parser import SmtLibParser
from antlr4 import *
from parser.generated.SMTLIBv2Lexer import SMTLIBv2Lexer
from parser.MySMTLIBv2Parser import *
from parser.generated.SMTLIBv2Listener import SMTLIBv2Listener
from parser.HermesListener import HermesListener
from parser.generated.SMTLIBv2Visitor import SMTLIBv2Visitor
from parser.HermesVisitor import HermesVisitor
from typing import *
from pysmt.oracles import get_logic
from pysmt.rewritings import conjunctive_partition
from portfolio_solver import PortfolioSolver
import reasoning_graph

pp = pprint.PrettyPrinter(indent=4)


def removeAnnotations(input_file):
    input = FileStream(input_file)
    lexer = SMTLIBv2Lexer(input)
    stream = CommonTokenStream(lexer)
    parser = MySMTLIBv2Parser(stream)
    tree = parser.start()
    str = ''
    hermesListener = HermesListener(str)
    walker = ParseTreeWalker()
    walker.walk(hermesListener, tree)
    return hermesListener.str



def strip_file(filename):
    with open(filename, "r") as f:
        strfile = f.read()
    newstrfile = []
    for line in strfile.split("\n"):
        tmpline = [x for x in line.split(" ") if x != ""]
        newstrfile.append(" ".join(tmpline))
    with open(filename, "w") as f:
        f.write("\n".join(newstrfile))

def process_file(input_file, no_ann_file):
    inputNoAnn = removeAnnotations(input_file)
    inputNoAnnFile = open(no_ann_file, 'w')
    inputNoAnnFile.write(inputNoAnn)
    inputNoAnnFile.close()
    strip_file(no_ann_file)

    parser = SmtLibParser()
    script = parser.get_script_fname(no_ann_file)

    formula = script.get_last_formula()

    formulas = get_all_conjuncts(formula)
    portfolio_solver = PortfolioSolver(formulas)
    satunsat = portfolio_solver.solve()
    print(satunsat)

def get_all_conjuncts(formula):
    result = set([])
    get_all_conjuncts_rec(formula, result)
    return result

def get_all_conjuncts_rec(formula, result):
    if (formula.node_type() is op.AND):
        for conjunct in formula.args():
            get_all_conjuncts_rec(conjunct, result)
    else:
        result.add(formula)

def main(args):
    parser = argparse.ArgumentParser(description='Hermes')
    parser.add_argument('input_file', metavar='program', type=str,
                        help='the input file describing the program')
    parser.set_defaults(no_ann="no_ann.tmp")
    parser.add_argument('-n', '--no-ann', metavar='no_ann', type=str,
                        nargs='?',
                        help='smtlib file without annotations')
    args = parser.parse_args(args)
    if len(sys.argv) == 1:
        parser.print_help()
        exit(1)
    process_file(args.input_file, args.no_ann)


if __name__ == '__main__':
    main(sys.argv[1:])
