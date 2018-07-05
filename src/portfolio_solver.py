import os
import subprocess
from pysmt.logics import QF_NRA, QF_NIRA
from pysmt.shortcuts import Solver, get_env, And, Symbol
from pysmt.exceptions import SolverReturnedUnknownResultError
from enum import Enum
from six.moves import cStringIO
from transcendental import ExtendedEnvironment, reset_env
from transcendental import ExtendedSmtLibParser
from pysmt.printers import HRPrinter
from pysmt.rewritings import PrenexNormalizer, Ackermanization, Skolemization
from pysmt.rewritings import Purifications
from pysmt.smtlib.script import SmtLibScript
from pysmt.smtlib.printers import SmtPrinter, LimitedSmtPrinter
from pysmt.smtlib.printers import to_smtlib
from trivalogic import TriValLogic, Values
import transcendental
import z3
import pprint
DREAL_NAME = "dreal"
DREAL_PATH = "/home/yoniz/git/dreal/bin/dReal"
DREAL_ARGS = "--in"
DREAL_LOGICS = [QF_NRA, QF_NIRA]

pp = pprint.PrettyPrinter(indent=4)

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


class PartitionStrategy:
    def __init__(self, formulas):
        self._formulas = formulas
        self._solvers_to_sets_of_formulas = {}
        self._generate_internal_map()

    def _add_formulas_to_solver(self, solver, formulas):
        if solver in self._solvers_to_sets_of_formulas.keys():
            self._solvers_to_sets_of_formulas[solver].update(formulas)
        else:
           self._solvers_to_sets_of_formulas[solver] = formulas

    def formulas_for_solver(self, solver_name):
        return self._solvers_to_sets_of_formulas[solver_name]

    def get_solvers(self):
        return self._solvers_to_sets_of_formulas.keys()

    def _generate_internal_map(self):
        raise NotImplementedError("This is an interface!")


class SimpleTheoryStrategy(PartitionStrategy):
    def __init__(self, formulas=None):
        self._env = get_env()
        self._ackermanization = Ackermanization()
        super().__init__(formulas)

    def _generate_internal_map(self):
        for formula in self._formulas:
            solver = self._solve_formula_with(formula)
            if solver == 'dreal':
                h = Skolemization(self._env)
                skolemized_formula = h.simple_skolemization(formula)
                ackermized_formula = self._ackermanization.do_ackermanization(skolemized_formula)
                self._add_formulas_to_solver(solver, set([ackermized_formula]))
            else:
                self._add_formulas_to_solver(solver, set([formula]))

    def _solve_formula_with(self, formula):
        theory = self._env.theoryo.get_theory(formula)
        q_oracle = self._env.qfo
        if theory.linear:
            result = 'z3'
        else:
            result = 'dreal'
        return result

class TransStrategy(PartitionStrategy):
    def __init__(self, formulas=None):
        self._env = get_env()
        super().__init__(formulas)

    def _generate_internal_map(self):
        for formula in self._formulas:
            solver = self._solve_formula_with(formula)
            self._add_formulas_to_solver(solver, set([formula]))

    def _solve_formula_with(self, formula):
        if transcendental.includes_trans(formula):
            return 'dreal'
        else:
            return 'z3'



class TypeStratedy(PartitionStrategy):
    def __init__(self, formulas):
        self._all_inner_types = InnerType.get_all_inner_types()
        self._map_inner_types_to_solvers()
        super().__init__(formulas)

    def _generate_internal_map(self):
        formulas = self._formulas
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




class PortfolioSolver:
    def __init__(self, smtlib_str):
        stream = cStringIO(smtlib_str)
        self._env = reset_env()
        self._add_dreal()
        #script = self._get_script(stream, False)
        parser = ExtendedSmtLibParser(environment=self._env)
        script = parser.get_script(stream)
        formula = script.get_last_formula()
        #uncommented line is for splitting a problem.
        #formulas = formula.args()
        formulas = [formula]
        self._strategy = TransStrategy(formulas)
        self._smtlib = smtlib_str

    def _get_script(self, stream, optimize):
        #get script
        parser = ExtendedSmtLibParser(environment=self._env)
        script = parser.get_script(stream)
        #the internal representation of the formula inlines define-fun
        formula = script.get_last_formula()

        declarations = []
        declarations.extend(script.filter_by_command_name("declare-sort"))
        declarations.extend(script.filter_by_command_name("declare-fun"))
        declarations.extend(script.filter_by_command_name("declare-const"))

        new_script = SmtLibScript()

        for declaration in declarations:
            new_script.add_command(declaration)
        if (optimize):
            #remove quantifiers
            prenex_normalizer = PrenexNormalizer()
            quantifications, matrix = prenex_normalizer.walk(formula)
            quantifier, variables = quantifications[0]
            assert (quantifier == self._env.formula_manager.Exists)
            assert (len(quantifications) == 1)
            env = get_env()
            mgr = env.formula_manager
            subs = dict((x, mgr.FreshSymbol(x.symbol_type())) for x in variables)
            for key in subs.keys():
                new = subs[key]
                new_script.add("declare-fun", [new])
            substitued_matrix = matrix.substitute(subs)
            new_script.add("assert", [substitued_matrix])

        else:
            new_script.add("assert", [formula])

        new_script.add("check-sat", [])

        buf2 = cStringIO()
        new_script.serialize(buf2, False)
        smtlib_data = buf2.getvalue()




        return new_script




    def _add_dreal(self):
        env = get_env()
        env.factory.add_generic_solver(DREAL_NAME, [DREAL_PATH, DREAL_ARGS], DREAL_LOGICS)


    #include only purely real and int formulas
    def _filter_formulas(self, formulas):
        filtered_formulas = []
        for f in formulas:
            fvars = f.get_free_variables()
            f_is_clean = True
            for v in fvars:
                vtype = v.symbol_type()
                if not (vtype.is_real_type() or vtype.is_int_type()):
                    f_is_clean = False
                    break
            if f_is_clean:
                filtered_formulas.append(f)
        return filtered_formulas


    def _solve_with_dreal(self, formula):
        #ackermanization
        ackermanization = Ackermanization()
        h = Skolemization(self._env)
        skolemized_formula = h.simple_skolemization(formula)
        ackermized_formula = ackermanization.do_ackermanization(skolemized_formula)
        pure_formula = Purifications.real_int_purify(ackermized_formula)
        #filtered_formulas = self._filter_formulas(formulas)
        #formula = And(filtered_formulas)
        limited_smt_printer = LimitedSmtPrinter()
        smtlib_data = "(set-logic QF_NRA)\n" + limited_smt_printer.printer(pure_formula)

        #dreal doesn't like to_real
        smtlib_data = smtlib_data.replace('to_real', '* 1 ')
        try:
            os.remove('dreal_tmp.smt2')
        except OSError:
            pass
        open('dreal_tmp.smt2', 'w').write(smtlib_data)
        result_object = subprocess.run([DREAL_PATH, '--model', 'dreal_tmp.smt2'], stdout=subprocess.PIPE)
        result_string = result_object.stdout.decode('utf-8')
        result = self._parse_result_from_dreal(result_string)

        #take care of (get-value)s
        values = []
        if result == SolverResult.SAT:
            #get dreal solution
            raw_values = self._parse_values_from_dreal(result_string)
            #get list of wanted values
            stream = cStringIO(self._smtlib)
            parser = ExtendedSmtLibParser(environment=self._env)
            script = parser.get_script(stream)
            exprs = []
            dreal_exprs = set([])
            for get_val_cmd in script.filter_by_command_name("get-value"):
                exprs.extend(get_val_cmd.args)
            for expr in exprs:
                if expr in ackermanization._terms_to_consts:
                    dreal_expr = ackermanization._terms_to_consts[expr]
                    dreal_exprs.add(dreal_expr)
            #get wanted values from the solution
            for expr in exprs:
                try:
                    values.append(raw_values[ackermanization._terms_to_consts[expr]])
                except KeyError:
                    values.append('__')
        return result, values

    def _parse_result_from_dreal(self, result_string):
        if "unsat" in result_string:
            return SolverResult.UNSAT
        elif "sat" in result_string:
            return SolverResult.SAT
        elif "unknown" in result_string:
            return SolverResult.UNKNOWN
        else:
            assert(False)

    def _parse_values_from_dreal(self, result_string):
        raw_values = {}
        for line in result_string.splitlines()[1:-1]:
            var_part, middle_part, value_part = self._get_parts(line)
            assert(middle_part == "[ ENTIRE ]")
            v = self._env.formula_manager.get_symbol(var_part)
            raw_values[v] = value_part
        return raw_values

    def _get_parts(self, line):
        var_part, the_rest = line.split(" : ")
        middle_part, value_part = the_rest.split(" = ")
        return var_part, middle_part, value_part




    def _solve_partitioned_problem(self):
        result = SolverResult.SAT
        values = []
        for solver_name in self._strategy.get_solvers():
            formulas = self._strategy.formulas_for_solver(solver_name)
            formula = And(formulas)
            if solver_name == 'dreal':
                result, values = self._solve_with_dreal(formula)
            else:
                solver = Solver(solver_name)
                solver.add_assertion(formula)
                try:
                    solver_result = solver.solve()
                    if solver.solve() is False:
                        result = SolverResult.UNSAT
                        break
                except SolverReturnedUnknownResultError:
                    print(solver_name, ': unknown')
                    result = SolverResult.UNKNOWN
                    break
                values.extend(self.get_values(solver))
            print(solver_name,': ', result, values)
        return result, values

    def solve(self):
        return self._solve_partitioned_problem()

    def get_values(self, solver):
        stream = cStringIO(self._smtlib)
        parser = ExtendedSmtLibParser(environment=self._env)
        script = parser.get_script(stream)
        exprs = []
        for get_val_cmd in script.filter_by_command_name("get-value"):
            exprs.extend(get_val_cmd.args)
        #values = solver.get_values(exprs)
        values = []
        for expr in exprs:
            try:
                value = solver.get_value(expr)
            except (z3.Z3Exception) as e: #comma separated list of exceptions
                value = "__"
            values.append(self._regulate(value))
        return values

    def _regulate(self, value):
        if str(value).lower() == 'true':
            return Values.to_string(Values.TRUE)
        elif str(value).lower() == 'false':
            return Values.to_string(Values.FALSE)
        else:
            return value

    def _get_free_variables_of_formulas(formulas):
        result = set([])
        for formula in formulas:
            result.add(formula.get_free_variables())
        return result

    def _map_variables_to_formulas(formulas):
        variables_to_sets_of_formulas = {}
        for f in formulas:
            variables = f.get_free_variables()
            for v in variables:
                if v not in variables_to_sets_of_formulas:
                    variables_to_sets_of_formulas[v] = set([])
                variables_to_sets_of_formulas[v].add(f)
        return variables_to_sets_of_formulas


