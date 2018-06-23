import sys
import argparse
import pprint
from pysmt.shortcuts import Solver
import pysmt.operators as op
from pysmt.smtlib.parser import SmtLibParser
from pysmt.logics import *
from pysmt.exceptions import SolverReturnedUnknownResultError
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

pp = pprint.PrettyPrinter(indent=4)


class InnerType:
    def __init__(self, is_array=False, is_bv=False, is_int=False):
        self.is_array = is_array
        self.is_bv = is_bv
        self.is_int = is_int

    def __hash__(self):
        return hash((self.is_array, self.is_bv, self.is_int))

    def __eq__(self, other):
        return (self.is_array, self.is_bv, self.is_int) == \
    (other.is_array, other.is_bv, other.is_int)

    def __ne__(self, other):
        return not(self == other)

    def __str__(self):
        res = '{ '
        if self.is_array:
            res+='arrays '
        if self.is_bv:
            res +='bv '
        if self.is_int:
            res += 'int '
        res += '}'
        return res

    def __repr__(self):
        return self.__str__()

    def get_all_inner_types():
        all_inner_types = set([])
        all_inner_types.add(InnerType(True, True, True))
        all_inner_types.add(InnerType(True, True, False))
        all_inner_types.add(InnerType(True, False, True))
        all_inner_types.add(InnerType(True, False, False))
        all_inner_types.add(InnerType(False, True, True))
        all_inner_types.add(InnerType(False, True, False))
        all_inner_types.add(InnerType(False, False, True))
        all_inner_types.add(InnerType(False, False, False))
        return all_inner_types

    def get_inner_type_of_formulas(formulas, formulas_to_inner_types):
        result = InnerType()
        for f in formulas:
            if formulas_to_inner_types[f].is_array:
                result.is_array = True
            if formulas_to_inner_types[f].is_bv:
                result.is_bv = True
            if formulas_to_inner_types[f].is_int:
                result.is_int = True
        return result

    def inner_type_of_formula(formula):
        formula_inner_type = InnerType()
        for v in formula.get_free_variables():
            var_type = v.symbol_type()
            if var_type.is_array_type():
                formula_inner_type.is_array = True
            if var_type.is_bv_type():
                formula_inner_type.is_bv = True
            if var_type.is_int_type():
                formula_inner_type.is_int = True
        return formula_inner_type


    def get_inner_typed_formulas_from_formulas(formulas):
        result = {}
        for formula in formulas:
            result[formula] = InnerType.inner_type_of_formula(formula)
        return result

class PortfolioSolver:
    def __init__(self, formulas):
        self._all_inner_types = InnerType.get_all_inner_types()
        self._map_inner_types_to_solvers()
        self._map_solvers_to_formulas(formulas)

    def _map_inner_types_to_solvers(self):
        self._inner_type_to_solver = {}
        for it in self._all_inner_types:
            if it.is_bv:
                if it.is_int:
                    self._inner_type_to_solver[it] = "cvc4"
                else:
                    self._inner_type_to_solver[it] = "cvc4"
            else:
                if it.is_int:
                    self._inner_type_to_solver[it] = "cvc4"
                else:
                    self._inner_type_to_solver[it] = "cvc4"

    def _solve_partitioned_problem(self):
        result = "SAT"
        for solver_name in self._solvers_to_sets_of_formulas.keys():
            solver = Solver(solver_name)
            formulas = self._solvers_to_sets_of_formulas[solver_name]
            for formula in formulas:
                solver.add_assertion(formula)
            try:
                solver_result = solver.solve()
                print(solver_name, ': ', solver_result)
                if solver.solve() is False:
                    result = "UNSAT"
                    break
            except SolverReturnedUnknownResultError:
                print(solver_name, ': unknown')
                result = "UNKNOWN"
                break
        return result

    def solve(self):
        return self._solve_partitioned_problem()

    def _map_solvers_to_formulas(self, formulas):
        variables = PortfolioSolver._get_free_variables_of_formulas(formulas)
        self._solvers_to_sets_of_formulas = {}
        formulas_to_inner_types = InnerType.get_inner_typed_formulas_from_formulas(formulas)
        variables_to_formulas = PortfolioSolver._map_variables_to_formulas(formulas)
       # inner_types_to_sets_of_formulas = map_inner_types_to_formulas(variables_to_sets_of_formulas, formulas)
       # pp.pprint(inner_types_to_sets_of_formulas)
        for variable in variables_to_formulas.keys():
            formulas_of_variable = variables_to_formulas[variable]
            inner_type_of_formulas = InnerType.get_inner_type_of_formulas(formulas_of_variable, formulas_to_inner_types)
            solver = self._inner_type_to_solver[inner_type_of_formulas]
            #solver = 'z3'
            self._add_formulas_to_solver(solver, formulas_of_variable)

    def _get_free_variables_of_formulas(formulas):
        result = set([])
        for formula in formulas:
            result.add(formula.get_free_variables())
        return result

    def _add_formulas_to_solver(self, solver, formulas):
        if solver in self._solvers_to_sets_of_formulas.keys():
            self._solvers_to_sets_of_formulas[solver].update(formulas)
        else:
           self._solvers_to_sets_of_formulas[solver] = formulas


    def _map_variables_to_formulas(formulas):
        variables_to_sets_of_formulas = {}
        for f in formulas:
            variables = f.get_free_variables()
            for v in variables:
                if v not in variables_to_sets_of_formulas:
                    variables_to_sets_of_formulas[v] = set([])
                variables_to_sets_of_formulas[v].add(f)
        return variables_to_sets_of_formulas


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
    for f in formulas:
        print('************************************')
        for conj in conjunctive_partition(f):
            print('panda formula = ', conj.serialize(100))
            logic = get_logic(conj)
            print('panda ', f, ': ', logic)
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
