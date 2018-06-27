from pysmt.logics import QF_NRA, QF_NIRA
from pysmt.shortcuts import Solver, get_env
from pysmt.exceptions import SolverReturnedUnknownResultError
from enum import Enum
from six.moves import cStringIO
from pysmt.smtlib.parser import SmtLibParser

DREAL_NAME = "dreal"
DREAL_PATH = "/home/yoniz/git/dreal/bin/dReal"
DREAL_ARGS = "--in"
DREAL_LOGICS = [QF_NRA, QF_NIRA]


class SolverResult(Enum):
    SAT = 1
    UNSAT = 2
    UNKNOWN = 3

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
    def __init__(self, smtlib_str):
        stream = cStringIO(smtlib_str)
        parser = SmtLibParser()
        script = parser.get_script(stream)
        formula = script.get_last_formula()
        formulas = formula.args
        self._all_inner_types = InnerType.get_all_inner_types()
        self._map_inner_types_to_solvers()
        self._map_solvers_to_formulas(formulas)
        self._add_dreal()

    def _add_dreal(self):
        env = get_env()
        env.factory.add_generic_solver(DREAL_NAME, [DREAL_PATH, DREAL_ARGS], DREAL_LOGICS)

    def _map_inner_types_to_solvers(self):
        self._inner_type_to_solver = {}
        for it in self._all_inner_types:
            if it.is_bv:
                if it.is_int:
                    self._inner_type_to_solver[it] = "z3"
                else:
                    self._inner_type_to_solver[it] = "z3"
            else:
                if it.is_int:
                    self._inner_type_to_solver[it] = "z3"
                else:
                    self._inner_type_to_solver[it] = "z3"

    def _solve_partitioned_problem(self):
        result = SolverResult.SAT
        for solver_name in self._solvers_to_sets_of_formulas.keys():
            solver = Solver(solver_name)
            formulas = self._solvers_to_sets_of_formulas[solver_name]
            for formula in formulas:
                solver.add_assertion(formula)
            try:
                solver_result = solver.solve()
                print(solver_name, ': ', solver_result)
                if solver.solve() is False:
                    result = SolverResult.UNSAT
                    break
            except SolverReturnedUnknownResultError:
                print(solver_name, ': unknown')
                result = SolverResult.UNKNOWN
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


