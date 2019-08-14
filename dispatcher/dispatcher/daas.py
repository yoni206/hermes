import os
import dispatcher
import multiprocessing
from enum import Enum

TMP_DIR="tmp"

class LANG(Enum):
    SMTLIB = "smtlib"

class VerificationTask:
    def __init__(self):
        self.id = ""
        self.query = ""
        self.language = LANG.SMTLIB
        self.additional_options = ""

class VerificationResult:
    def __init__(self):
        self.id = ""
        self.result = "unknown"
        self.explanation = ""

    def __str__(self):
        return (self.id + "\n" + self.result + "\n" + self.explanation)

#arg task is a VerificationTask
#result is a VerificationResult
def verify(task):
    filename = task.id + ".smt2"
    if not os.path.exists(TMP_DIR):
        os.makedirs(TMP_DIR)
    tmp_path = os.path.abspath(TMP_DIR + "/" + filename)
    with open(tmp_path, "w") as f:
        f.write(task.query)
    config = dispatcher.Config()
    config.ncpus = multiprocessing.cpu_count()
    config.verbose = False
    config.encoding = "plain"
    config.solvers = task.solvers
    config.models = True
    config.extra_options = task.additional_options
    config.benchmark = tmp_path
    disp_result_lines = dispatcher.solve_configuration(config)

    result = VerificationResult()
    result.id = task.id
    result.result = disp_result_lines[0]
    result.explanation = " ".join(disp_result_lines[1:])
    return result

def test1():
    with open("/home/yoniz/git/hermes/dispatcher/dispatcher/examples/bug.smt2", "r") as f:
        smtlib = f.read()
    task = VerificationTask()
    task.id = "test"
    task.query = smtlib
    task.language = LANG.SMTLIB
    task.solvers = ["all"]
    result = verify(task)
    print(result)


def test2():
    with open("/home/yoniz/git/hermes/dispatcher/dispatcher/examples/simple/simple_get_value.smt2") as f:
        smtlib = f.read()
    task = VerificationTask()
    task.id = "test"
    task.query = smtlib
    task.language = LANG.SMTLIB
    task.solvers = ["generic"]
    result = verify(task)
    print(result)

if __name__ == '__main__':
    test1()
