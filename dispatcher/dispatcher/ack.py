import sys
import pysmt
from pysmt.rewritings import PrenexNormalizer, Ackermannizer
from pysmt.smtlib.script import SmtLibScript
from pysmt.smtlib.parser import SmtLibParser
from six.moves import cStringIO


parser = SmtLibParser()

with open("/home/yoniz/git/hermes/dispatcher/dispatcher/examples/Assessment3_test1_QF.smt2", 'r') as f:
    smtlib_str = f.read();
stream = cStringIO(smtlib_str)
script = parser.get_script(stream)
formula = script.get_last_formula()
ackermanization = Ackermannizer()
ackermized_formula = ackermanization.do_ackermannization(formula)

