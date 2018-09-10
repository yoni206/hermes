from six.moves import cStringIO
from pysmt.logics import QF_NRA, QF_NIRA
from pysmt.smtlib.script import SmtLibScript, smtlibscript_from_formula
from pysmt.smtlib.parser import SmtLibParser
from pysmt.shortcuts import Solver, qelim, get_env
from pysmt.logics import QF_NRA
from pysmt.smtlib.commands import SET_LOGIC
import pysmt.smtlib.printers as printers
from pysmt.rewritings import PrenexNormalizer
from sys import argv

def get_value():
    solver = Solver('z3')
    parser = SmtLibParser()
    script = parser.get_script_fname("get_value.smt2")
    #result = script.evaluate(Solver('z3'))
    exprs = []
    for get_val_cmd in script.filter_by_command_name("get-value"):
        exprs.extend(get_val_cmd.args)
    formula = script.get_last_formula()
    solver.add_assertion(formula)
    result1 = solver.solve()
    result2 = solver.get_values(exprs)

def remove_quant_and_define_funs(path):
    parser = SmtLibParser()
    script = parser.get_script_fname(path)
    formula = script.get_last_formula()
    prenex_normalizer = PrenexNormalizer()
    quantifications, matrix = prenex_normalizer.walk(formula)
    quantifier, variables = quantifications[0]
    assert (len(quantifications) == 1)
    env = get_env()
    mgr = env.formula_manager
    subs = dict((x, mgr.FreshSymbol(x.symbol_type())) for x in variables)
    substitued_matrix = matrix.substitute(subs)

    declarations = []
    declarations.extend(script.filter_by_command_name("declare-sort"))
    declarations.extend(script.filter_by_command_name("declare-fun"))
    declarations.extend(script.filter_by_command_name("declare-const"))
    new_script = SmtLibScript()
    new_script.add(SET_LOGIC, [QF_NRA])
    for key in subs.keys():
        new = subs[key]
        new_script.add("declare-fun", [new])
    for declaration in declarations:
        new_script.add_command(declaration)
    new_script.add("assert", [substitued_matrix])
    new_script.add("check-sat", [])
    buf = cStringIO()
    new_script.serialize(buf, False)
    smtlib = buf.getvalue()
    print(smtlib)


DREAL_NAME = "dreal"
DREAL_PATH = "/home/yoniz/git/dreal/bin/dReal"
DREAL_ARGS = "--in"
DREAL_LOGICS = [QF_NRA, QF_NIRA]
def solve_with_dreal(formula):
        env = get_env()
        env.factory.add_generic_solver(DREAL_NAME, [DREAL_PATH, DREAL_ARGS], DREAL_LOGICS)
        solver = Solver('dreal')
        solver.add_assertion(formula)
        solver.solve()



if __name__ == "__main__":
    path = argv[1]
    parser = SmtLibParser()
    script = parser.get_script_fname(path)
    formula = script.get_last_formula()
    solve_with_dreal(formula)
