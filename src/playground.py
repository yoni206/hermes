from pysmt.shortcuts import Solver
from pysmt.smtlib.parser import SmtLibParser
from pysmt.oracles import get_logic
from sys import argv
import pysmt
from heuristics import SegmentsHeuristics

def main(path):
    parser = SmtLibParser()
    script = parser.get_script_fname(path)
    formula = script.get_last_formula()
    h = SegmentsHeuristics(formula, 'z3')
    l = h.try_to_unsatisfy()
    print(l)

if __name__ == "__main__":
    path = argv[1]
    main(path)
