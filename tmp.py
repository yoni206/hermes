from pysmt.smtlib.parser import SmtLibParser
import sys
from six.moves import cStringIO # Py2-Py3 Compatibility


with open('tmp.smt2') as f:
    content = f.read()

parser = SmtLibParser()
script = parser.get_script(cStringIO(content))
buf_out = cStringIO()
script.serialize(buf_out, daggify=False)
print(buf_out.getvalue())

