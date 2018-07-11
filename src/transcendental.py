#adding operators
from pysmt.operators import new_node_type

SIN = new_node_type(node_str="sin")
COS = new_node_type(node_str="cos")
ALL_TRANS = (SIN, COS)


#Extending FormulaManager
import pysmt.environment
import pysmt.formula

class ExtendedFormulaManager(pysmt.formula.FormulaManager):
    def Sin(self, arg):
        return self.create_node(node_type=SIN, args=(arg,))

    def Cos(self, arg):
        return self.create_node(node_type=COS, args=(arg,))


#updating some walkers with first approach
from pysmt.type_checker import SimpleTypeChecker
SimpleTypeChecker.set_handler(SimpleTypeChecker.walk_real_to_real, *ALL_TRANS)

from pysmt.oracles import FreeVarsOracle
FreeVarsOracle.set_handler(FreeVarsOracle.walk_simple_args, *ALL_TRANS)

from pysmt.rewritings import PrenexNormalizer
PrenexNormalizer.set_handler(PrenexNormalizer.walk_theory_op, *ALL_TRANS)


#updating some walkers with second approach
import pysmt.printers
from pysmt.walkers.generic import handles
TRANS_TYPE_TO_STR = {SIN: "sin", COS: "cos"}

class ExtendedHRPrinter(pysmt.printers.HRPrinter):
    def walk_sin(self, formula):
        return self.walk_nary(formula, " sin ")

    def walk_cos(self, formula):
        return self.walk_nary(formula, " cos ")

    @handles(SIN, COS)
    def walk_trans(self, formula):
        node_type = formula.node_type()
        op_symbol = TRANS_TYPE_TO_STR[node_type]
        self.stream.write("(%s " % op_symbol)
        yield formula.arg(0)
        self.stream.write(")")

class ExtendedHRSerializer(pysmt.printers.HRSerializer):
    PrinterClass = ExtendedHRPrinter

from pysmt.oracles import TheoryOracle
class ExtendedTheoryOracle(TheoryOracle):
    def walk_sin(self, formula, args, **kwargs):
        return args[0].set_linear(False)

    def walk_cos(self, formula, args, **kwargs):
        return args[0].set_linear(False)


#updating some walkers with third approach
from pysmt.walkers import IdentityDagWalker
def walk_sin(self, formula, args, **kwargs): return self.mgr.Sin(args[0])
def walk_cos(self, formula, args, **kwargs): return self.mgr.Cos(args[0])
IdentityDagWalker.set_handler(walk_sin, SIN)
IdentityDagWalker.set_handler(walk_cos, COS)



from pysmt.smtlib.printers import SmtPrinter
def walk_sin(self, formula): return self.walk_nary(formula, "sin")
def walk_cos(self, formula): return self.walk_nary(formula, "cos")
SmtPrinter.set_handler(walk_sin, SIN)
SmtPrinter.set_handler(walk_cos, COS)


#smtlib parser
from pysmt.smtlib.parser import SmtLibParser
class ExtendedSmtLibParser(SmtLibParser):
    def __init__(self, environment=None, interactive=False):
        super().__init__(environment, interactive)
        mgr = self.env.formula_manager
        self.interpreted[TRANS_TYPE_TO_STR[SIN]] = self._operator_adapter(mgr.Sin)
        self.interpreted[TRANS_TYPE_TO_STR[COS]] = self._operator_adapter(mgr.Cos)



#env
from pysmt.environment import Environment, pop_env, get_env
from pysmt.environment import push_env as pysmt_push_env

class ExtendedEnvironment(Environment):
    FormulaManagerClass = ExtendedFormulaManager
    HRSerializerClass = ExtendedHRSerializer
    SmtLibParserClass = ExtendedSmtLibParser
    TheoryOracleClass = ExtendedTheoryOracle

def push_env(env=None):
    if env is None:
        env = ExtendedEnvironment()
    return pysmt_push_env(env=env)

def reset_env():
    pop_env()
    push_env()
    return get_env()

#reset_env()

#returns true if the formula includes a transcendental function
def includes_trans(formula):
    if formula.node_type() == SIN or \
        formula.node_type == COS:
            return True
    else:
        for arg in formula.args():
            if includes_trans(arg):
                return True
        #no trans was found
        return False



if __name__ == "__main__":
    env = reset_env()
    mgr = env.formula_manager
    f = mgr.Sin(mgr.Real(5))
    print(f)
