from transcendental import ExtendedSmtLibParser
import traceback
import re
import os
import sys
import subprocess
from pysmt.logics import QF_NRA, QF_NIRA
from pysmt.shortcuts import Solver, get_env, And, Symbol
from pysmt.exceptions import SolverReturnedUnknownResultError, \
                       ConvertExpressionError, \
                       UnsupportedOperatorError, \
                       UnknownSolverAnswerError
from enum import Enum
from six.moves import cStringIO
from transcendental import ExtendedEnvironment, reset_env
from pysmt.printers import HRPrinter
from pysmt.rewritings import PrenexNormalizer, Ackermannizer, Skolemization
from pysmt.rewritings import Purifications
from pysmt.smtlib.script import SmtLibScript
from pysmt.smtlib.printers import SmtPrinter, LimitedSmtPrinter
from pysmt.smtlib.printers import to_smtlib
from pysmt.oracles import get_raw_logic
from trivalogic import TriValLogic, Values
import transcendental
import z3
import pprint
DREAL_BINARY = os.environ['DREAL_DIR'] + "/./dReal"
DREAL_TMP_SMT_PATH = 'dreal_tmp.smt2'
DREAL_MODEL_PATH = DREAL_TMP_SMT_PATH + '.model'

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
    def __init__(self, formulas, config):
        self._formulas = formulas
        self._solvers_to_sets_of_formulas = {}
        self._generate_internal_map()
        self.config = config

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
        for formula in self._formulas:
            solver = self._solve_formula_with(formula)
            self._add_formulas_to_solver(solver, set([formula]))
    
class StrategyFactory:
    STRATEGY_NAMES = ["transcendental", "always-z3", "always-yices", "always-cvc4", "always-dreal"]
    def get_strategy_by_name(name, formulas=None, disabled_solvers = []):
        if name == "transcendental":
            return TransStrategy(formulas, disabled_solvers)
        elif name == "always-z3":
            return AlwaysZ3Strategy(formulas)
        elif name == "always-yices":
            return AlwaysYicesStrategy(formulas)
        elif name == "always-cvc4":
            return AlwaysCVC4Strategy(formulas)
        elif name == "always-dreal":
            return AlwaysDrealStrategy(formulas)
        else:
            Assert(False)

class SimpleTheoryStrategy(PartitionStrategy):
    def __init__(self, formulas=None):
        self._env = get_env()
        self._ackermanization = Ackermannizer()
        super().__init__(formulas)

    def _generate_internal_map(self):
        for formula in self._formulas:
            solver = self._solve_formula_with(formula)
            if solver == 'dreal':
                h = Skolemization(self._env)
                skolemized_formula = h.simple_skolemization(formula)
                ackermized_formula = self._ackermanization.do_ackermannization(skolemized_formula)
                self._add_formulas_to_solver(solver, set([ackermized_formula]))
            else:
                self._add_formulas_to_solver(solver, set([formula]))

    def _solve_formula_with(self, formula):
        theory = self._env.theoryo.get_theory(formula)
        q_oracle = self._env.qfo
        if theory.linear:
            result = 'yices'
        else:
            result = 'dreal'
        return result

class TransStrategy(PartitionStrategy):
    def __init__(self, formulas=None, disabled_solvers = []):
        self._env = get_env()
        self._disabled_solvers = disabled_solvers
        super().__init__(formulas, disabled_solvers)
        assert('z3' not in disabled_solvers)


    def _solve_formula_with(self, formula):
        if 'dreal' in self._disabled_solvers:
            return 'z3'
        else:
            if transcendental.includes_trans(formula):
                return 'dreal'
            else:
                return 'z3'


class AlwaysZ3Strategy(PartitionStrategy):
    def __init__(self, formulas=None):
        self._env = get_env()
        self._disabled_solvers = []
        super().__init__(formulas, [])

    def _solve_formula_with(self, formula):
        return 'z3'



class AlwaysDrealStrategy(PartitionStrategy):
    def __init__(self, formulas=None):
        self._env = get_env()
        self._disabled_solvers = []
        super().__init__(formulas, [])

    def _solve_formula_with(self, formula):
        return 'dreal'

class AlwaysCVC4Strategy(PartitionStrategy):
    def __init__(self, formulas=None):
        self._env = get_env()
        self._disabled_solvers = []
        super().__init__(formulas, [])

    def _solve_formula_with(self, formula):
        return 'cvc4'


class AlwaysYicesStrategy(PartitionStrategy):
    def __init__(self, formulas=None):
        self._env = get_env()
        self._disabled_solvers = []
        super().__init__(formulas, [])

    def _solve_formula_with(self, formula):
        return 'yices'


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
    def __init__(self, smtlib_str, config, name):
        stream = cStringIO(smtlib_str)
        #count number of calls to solving, for file names
        self._env = reset_env()
        self._env.enable_infix_notation = True
        self._config = config
        self._name = name
        #script = self._get_script(stream, False)
        parser = ExtendedSmtLibParser(environment=self._env)
        script = parser.get_script(stream)
        formula = script.get_last_formula()
        #commented line is for splitting a problem.
        #formulas = formula.args()
        formulas = [formula]
        if config.strategy is not None:
            self._strategy = StrategyFactory.get_strategy_by_name(config.strategy, formulas)
        else:
            self._strategy = TransStrategy(formulas, config.disabled_solvers)
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




#    def _add_dreal(self):
#        env = get_env()
#        env.factory.add_generic_solver(DREAL_NAME, [DREAL_PATH, DREAL_ARGS], DREAL_LOGICS)


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
        ackermanization = Ackermannizer()
        h = Skolemization(self._env)
        skolemized_formula = h.simple_skolemization(formula)
        ackermized_formula = ackermanization.do_ackermannization(skolemized_formula)
        pure_formula = Purifications.real_int_purify(ackermized_formula)
        #filtered_formulas = self._filter_formulas(formulas)
        #formula = And(filtered_formulas)
        limited_smt_printer = LimitedSmtPrinter()
        smtlib_data = "(set-logic QF_NRA)\n" + limited_smt_printer.printer(pure_formula)

        #dreal doesn't like to_real
        smtlib_data = smtlib_data.replace('to_real', '* 1 ')
        try:
            os.remove(DREAL_TMP_SMT_PATH)
        except OSError:
            pass
        try: os.remove(DREAL_MODEL_PATH)
        except OSError:
            pass
        open(DREAL_TMP_SMT_PATH, 'w').write(smtlib_data)
        dreal_command = [DREAL_BINARY]
        dreal_command.append("--model")
        if self._config.dreal_precision:
            dreal_command.extend(["--precision", self._config.dreal_precision])
        dreal_command.append(DREAL_TMP_SMT_PATH)
        result_object = subprocess.run(dreal_command, stdout=subprocess.PIPE)
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
            #dreal_exprs = set([])
            for get_val_cmd in script.filter_by_command_name("get-value"):
                exprs.extend(get_val_cmd.args)
            for expr in exprs:
                if expr in ackermanization.get_term_to_const_dict():
                    dreal_expr = ackermanization.get_term_to_const_dict()[expr]
                    #dreal_exprs.add(dreal_expr)
                    if dreal_expr in raw_values:
                        value = raw_values[dreal_expr]
                    else:
                        value = '__'
                else:
                    value = '__'

                values.append(value)
        values_no_spaces = [str(x).replace(' ', '') for x in values]
        return result, values_no_spaces

    def _parse_result_from_dreal(self, result_string):
        if "unsat" in result_string:
            return SolverResult.UNSAT
        elif "sat" in result_string:
            return SolverResult.SAT
        elif "unknown" in result_string:
            return SolverResult.UNKNOWN
        else:
            #maybe the result is in *.model file.
            try:
                with open(DREAL_MODEL_PATH, 'r') as model_file:
                    dreal_model_string = model_file.read()
                if "sat" in dreal_model_string:
                    return SolverResult.SAT
            except OSError:
                pass
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


    def _solve_with_api(self, formula, solver):
        had_expression_error = False
        values = []
        try:
            solver.add_assertion(formula)
        except ConvertExpressionError as e:
            match_obj = re.match(r'.*Unsupported operator \'(.*)\' ', e.message, re.M)
            expr = match_obj.group(1)
            result = SolverResult.UNKNOWN
            values = [expr]
            had_expression_error = True
        if not had_expression_error:
            try:
              solver_result = solver.solve()
              if solver_result == False:
                  result = SolverResult.UNSAT
              else:
                  result = SolverResult.SAT
                  values.extend(self.get_values(solver))
            except SolverReturnedUnknownResultError:
              result = SolverResult.UNKNOWN
        return result, values


    def _solve_generic(self, smtlib_path, solver):
        try:
            values = []
            solver_result, values = solver.solve_smtlib_file(smtlib_path)
            if solver_result == False:
                result = SolverResult.UNSAT
            else:
                result = SolverResult.SAT
        except SolverReturnedUnknownResultError:
             result = SolverResult.UNKNOWN
        except UnknownSolverAnswerError as e:
             match_obj = re.match(r'.*undefined term: (.*)\"', str(e), re.M)
             expr = match_obj.group(1)
             result = SolverResult.UNKNOWN
             values = [expr]
        return result, values

    def get_value_lines(self):
        stream = cStringIO(self._smtlib)
        parser = ExtendedSmtLibParser(environment = self._env)
        script = parser.get_script(stream)
        exprs = []
        for get_val_cmd in script.filter_by_command_name("get-value"):
            exprs.extend(to_smtlib(a, False) for a in get_val_cmd.args)
        return "(get-value (" + " ".join(exprs)  +"))"

    def get_def_fun_lines(self):
        stream = cStringIO(self._smtlib)
        parser = ExtendedSmtLibParser(environment = self._env)
        script = parser.get_script(stream)
        lines = []
        for def_fun_cmd in script.filter_by_command_name("define-fun"):
            outstream = cStringIO()
            def_fun_cmd.serialize(daggify=False, outstream=outstream)
            lines.append(outstream.getvalue())
            #exprs.extend(to_smtlib(a, False) for a in get_val_cmd.args)
        return lines


    def _get_smtlib_content(self, formula):
        limited_smt_printer = LimitedSmtPrinter()
        original_def_func_lines = "\n".join(self.get_def_fun_lines())
        smtlib_content = ""
        smtlib_content = smtlib_content + limited_smt_printer.printer(formula)
        #smtlib_content = smtlib_content + original_def_func_lines
        smtlib_content = smtlib_content + self.get_value_lines()
        return smtlib_content


    def _solve_formula_with_solver(self, formula, solver_name):
        formula = self.massage_formula(formula, solver_name)
        logic = get_raw_logic(formula, self._env)
        solver = Solver(solver_name, logic)
        smtlib_content = self._get_smtlib_content(formula)
        if 'cvc4' in solver_name: 
            smtlib_content = "(set-logic ALL)\n" + smtlib_content
        elif 'yices' in solver_name:
            smtlib_content = "(set-logic QF_UFNIRA)\n" + smtlib_content
        smtlib_path = solver_name + "_" + self._name +  "_tmp.smt2"
        open(smtlib_path, 'w').write(smtlib_content)
        smtlib_path = os.path.realpath(smtlib_path)
        if solver.is_generic():
            result, values = self._solve_generic(smtlib_path, solver)
        else:
            result, values = self._solve_with_api(formula, solver)
        return result, values
    
    def massage_formula(self, formula, solver_name):
        result = formula
        if solver_name == "yices" or solver_name == "cvc4":
            h = Skolemization(self._env)
            skolemized_formula = h.simple_skolemization(formula)
            result = skolemized_formula
        return result

    def _solve_partitioned_problem(self):
        result = SolverResult.SAT
        values = []
        for solver_name in self._strategy.get_solvers():
            formulas = self._strategy.formulas_for_solver(solver_name)
            formula = And(formulas)
            if solver_name == 'dreal':
                result, values = self._solve_with_dreal(formula)
            else:
                had_expression_error = False
                result, values = self._solve_formula_with_solver(formula, solver_name)
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


#ignore PendingDeprecationWarning. 
#This is a pysmt issue, that is expected to be fixed
#see https://github.com/pysmt/pysmt/issues/488
import warnings
warnings.filterwarnings("ignore", category=PendingDeprecationWarning) 
