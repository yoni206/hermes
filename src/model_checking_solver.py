import os
import subprocess

class ModelCheckingSolver:
    HOLDS = "holds"
    DOES_NOT_HOLD = "fails"
    UNKNOWN = "unknown"

    def __init__(self):
        self._raw_content = None
        self._exec_path = None

    def set_content(self, content):
        self._raw_content = content

    def solve(self):
        raise NotImplementedError("must be overriden")

    def _parse_result_from_solver(self, result_str):
        raise NotImplementedError("must be overriden")

class NuSmvSolver(ModelCheckingSolver):
    def __init__(self):
        super().__init__()
        self._exec_path = os.environ['NUSMV_DIR'] + "/./NuSMV"

    def solve(self):
        with open('tmp.nusmv', 'w') as the_file:
            the_file.write(self._raw_content)
        command = [self._exec_path]
        command.append("-coi")
        command.append("tmp.nusmv")
        result_object = subprocess.run(command, stdout=subprocess.PIPE)
        result_string = result_object.stdout.decode('utf-8')
        result, explanation = self._parse_result_from_solver(result_string)
        return result, explanation

    def _parse_result_from_solver(self, result_str):
        result_line = get_result_line(result_str)
        if result_line.strip().endswith("is true"):
            result = ModelCheckingSolver.HOLDS
            explanation = None
        elif result_line.strip().endswith("is false"):
            result = ModelCheckingSolver.DOES_NOT_HOLD
            explanation_lines = get_expl_lines(result_str)
            explanation = "\n".join(explanation_lines)
        else:
            assert(False)
        return result, explanation

def get_result_line(result_str):
    lines = result_str.splitlines()
    index = get_index_of_line_starting_with(lines, "-- specification")
    line = lines[index]
    return line

def get_expl_lines(result_str):
        lines = result_str.splitlines()
        index = get_index_of_line_starting_with(lines, "-- specification")
        result = lines[index+2:]
        return result

def get_index_of_line_starting_with(lines, prefix):
    result = -1
    for index in range(0, len(lines)):
        line = lines[index]
        if line.startswith(prefix):
            result = index
            break
    return result
