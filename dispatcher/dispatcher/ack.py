import sys
import pysmt
from pysmt.rewritings import PrenexNormalizer, Ackermannizer
from pysmt.smtlib.script import SmtLibScript
from pysmt.smtlib.parser import SmtLibParser
from pysmt.shortcuts import to_smtlib, write_smtlib
from six.moves import cStringIO


parser = SmtLibParser()

with open("/home/yoniz/git/hermes/dispatcher/dispatcher/examples/Assessment2/nodtbbg.smt2", 'r') as f:
    smtlib_str = f.read();
stream = cStringIO(smtlib_str)
script = parser.get_script(stream)
formula = script.get_last_formula()
ackermanization = Ackermannizer()
ackermized_formula = ackermanization.do_ackermannization(formula)
write_smtlib(ackermized_formula, "/home/yoniz/git/hermes/dispatcher/dispatcher/examples/Assessment2/nodtbbg_ack.smt2" )


