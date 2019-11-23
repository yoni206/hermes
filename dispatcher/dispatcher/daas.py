import json
import multiprocessing
import os
import subprocess
from enum import Enum

import dispatcher

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
                     "--timeout", "5", "--ind_print_cex", "true"]

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
    result = VerificationResult()
    result.id = task.id
    result.result = ""
    result.explanation = str(result_json)
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


def verify_lustre_file(file_name):
    with open(file_name) as f:
        lustre = f.read()
    task = VerificationTask()
    task.id = "test_json"
    task.query = lustre
    task.language = LANG.LUSTRE
    result = verify(task)
    print(result)


def test_json():
    verify_lustre_file("examples/lustre/SW_agree.LUS")


def s5b():
    verify_lustre_file("examples/lustre/S5b.lus")


def s5c():
    verify_lustre_file("examples/lustre/S5c.lus")


def s6():
    verify_lustre_file("examples/lustre/S6.lus")


def unknown():
    verify_lustre_file("examples/lustre/unknown.lus")


def bacteria1():
    verify_lustre_file("examples/lustre/bacteria1.lus")


def bacteria2():
    verify_lustre_file("examples/lustre/bacteria2.lus")


def array():
    verify_lustre_file("examples/lustre/array.lus")


def cruise_controller():
    verify_lustre_file("examples/lustre/CruiseController.lus")


def thermostat():
    verify_lustre_file("examples/lustre/Thermostat.lus")


def general():
    verify_lustre_file("examples/lustre/S6.lus")


if __name__ == '__main__':
    general()
