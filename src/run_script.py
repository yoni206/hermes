from pysmt.shortcuts import Solver
from pysmt.smtlib.parser import SmtLibParser
from sys import argv

def main(path, solver_name):
    solver = Solver(solver_name)
    parser = SmtLibParser()
    script = parser.get_script_fname(path)
    formula = script.get_last_formula()
    solver.add_assertion(formula)
    result = solver.solve()
    print(result)


if __name__ == "__main__":
    path = argv[1]
    solver_name = argv[2]
    main(path, solver_name)
