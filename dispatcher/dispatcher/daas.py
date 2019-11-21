import os
import dispatcher
import multiprocessing
import subprocess
from enum import Enum
import json
from kind2 import *

TMP_DIR = "tmp"


class LANG(Enum):
    SMTLIB = "smtlib"
    LUSTRE = "lustre"


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


# arg task is a VerificationTask
# result is a VerificationResult
def verify_smt(task):
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


def verify_lustre(task):
    script_dir = os.path.dirname(os.path.realpath(__file__))
    solvers_dir = script_dir + "/solvers"
    kind2_command = [solvers_dir + "/model_checkers/kind2", "-json", "--modular", "true", "--compositional", "true",
                     "--timeout", "5"]

    filename = task.id + ".LUS"
    if not os.path.exists(TMP_DIR):
        os.makedirs(TMP_DIR)
    tmp_path = os.path.abspath(TMP_DIR + "/" + filename)
    with open(tmp_path, "w") as f:
        f.write(task.query)
    kind2_command.append(tmp_path)
    result_object = subprocess.run(kind2_command, stdout=subprocess.PIPE)
    result_string = result_object.stdout.decode('utf-8')
    # ignore warnings:
    result_string = result_string[result_string.find("["):]
    result_json = json.loads(result_string)
    kind2_result = analyze_json_result(result_json)
    kind2_result.analyze()
    result = VerificationResult()
    result.id = task.id
    result.result = ""
    result.explanation = str(kind2_result)
    return result


def verify(task):
    if task.language == LANG.SMTLIB:
        return verify_smt(task)
    elif task.language == LANG.LUSTRE:
        return verify_lustre(task)
    else:
        assert (False)


def test1():
    with open("/home/yoniz/git/hermes/dispatcher/dispatcher/examples/bug.smt2", "r") as f:
        smtlib = f.read()
    task = VerificationTask()
    task.id = "test1"
    task.query = smtlib
    task.language = LANG.SMTLIB
    task.solvers = ["all"]
    result = verify(task)
    print(result)


def test2():
    with open("/home/yoniz/git/hermes/dispatcher/dispatcher/examples/simple/simple_get_value.smt2") as f:
        smtlib = f.read()
    task = VerificationTask()
    task.id = "test2"
    task.query = smtlib
    task.language = LANG.SMTLIB
    task.solvers = ["generic"]
    result = verify(task)
    print(result)


def test_json():
    with open("examples/lustre/SW_agree.LUS") as f:
        lustre = f.read()
    task = VerificationTask()
    task.id = "test_json"
    task.query = lustre
    task.language = LANG.LUSTRE
    result = verify(task)
    print(result)


def s1():
    with open("examples/lustre/S1.lus") as f:
        lustre = f.read()
    task = VerificationTask()
    task.id = "test_door_lock"
    task.query = lustre
    task.language = LANG.LUSTRE
    result = verify(task)
    print(result)


def test_door_lock2():
    with open("examples/lustre/Door_lock_S2.lus") as f:
        lustre = f.read()
    task = VerificationTask()
    task.id = "test_door_lock"
    task.query = lustre
    task.language = LANG.LUSTRE
    result = verify(task)
    print(result)


def test_door_lock3():
    with open("examples/lustre/Door_lock_S3.lus") as f:
        lustre = f.read()
    task = VerificationTask()
    task.id = "test_door_lock"
    task.query = lustre
    task.language = LANG.LUSTRE
    result = verify(task)
    print(result)


def test_door_lock5():
    with open("examples/lustre/Door_lock_S1.lus") as f:
        lustre = f.read()
    task = VerificationTask()
    task.id = "test_door_lock"
    task.query = lustre
    task.language = LANG.LUSTRE
    result = verify(task)
    print(result)


def s5():
    with open("examples/lustre/S5.lus") as f:
        lustre = f.read()
    task = VerificationTask()
    task.id = "s6"
    task.query = lustre
    task.language = LANG.LUSTRE
    result = verify(task)
    print(result)



def s5b():
    with open("examples/lustre/S5b.lus") as f:
        lustre = f.read()
    task = VerificationTask()
    task.id = "s6"
    task.query = lustre
    task.language = LANG.LUSTRE
    result = verify(task)
    print(result)


def s6():
    with open("examples/lustre/S6.lus") as f:
        lustre = f.read()
    task = VerificationTask()
    task.id = "s6"
    task.query = lustre
    task.language = LANG.LUSTRE
    result = verify(task)
    print(result)


def unknown():
    with open("examples/lustre/unknown.lus") as f:
        lustre = f.read()
        task = VerificationTask()
        task.id = "s6"
        task.query = lustre
        task.language = LANG.LUSTRE
        result = verify(task)
        print(result)


def bacteria1():
    with open("examples/lustre/bacteria1.lus") as f:
        lustre = f.read()
        task = VerificationTask()
        task.id = "s6"
        task.query = lustre
        task.language = LANG.LUSTRE
        result = verify(task)
        print(result)


def bacteria2():
    with open("examples/lustre/bacteria2.lus") as f:
        lustre = f.read()
        task = VerificationTask()
        task.id = "s6"
        task.query = lustre
        task.language = LANG.LUSTRE
        result = verify(task)
        print(result)


if __name__ == '__main__':
    bacteria1()
