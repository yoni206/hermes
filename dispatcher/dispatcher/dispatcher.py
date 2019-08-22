#based on https://github.com/Boolector/boolector/blob/smtcomp19/contrib/poolector.py
import argparse
import multiprocessing
import subprocess
import sys
import time
import signal
import os
import re
from enum import Enum

pool = None

class Config:
    def __init__(self):
        pass

class SOLVER_MODE(Enum):
    COMPETITION = 1
    BINARY = 2
    MODELS = 3

g_result = None
script_dir = os.path.dirname(os.path.realpath(__file__))
solvers_dir = script_dir + "/solvers"
starexec_suffix = "starexec_run_default"



def get_solver_command(config, solver_name, solver_mode, extra_options=""):
    assert(solver_name in ALL_NAMES)
    assert(not (solver_mode == SOLVER_MODE.COMPETITION and extra_options != []))
    result = NAMES_AND_MODES_TO_COMMANDS[solver_name][solver_mode]
    assert(result != None)
    result.extend(extra_options)
    return result



CVC4_NAME = "cvc4"
CVC4_FMF_NAME = "cvc4_fmf"
YICES_NAME = "yices"
BOOLECTOR_NAME = "boolector"
VERIT_NAME = "verit"
SPASSSATT_NAME = "spasssatt"
MATHSAT_NAME = "mathsat"
Z3_NAME = "z3"
#having issues with this one
#CTRLERGO_NAME = "ctrlergo"
#select solver based on benchmark
NORMAL_NAME = "normal"
#use cvc4
GENERIC_NAME = "generic"
#use all solvers
ALL_NAME = "all"

#for each solver we have its competition script and its binary
#by default we use the competition script
#for models, we use the binary
#also, for special options, we use binary
cvc4_comp_script = solvers_dir + "/comp/CVC4-2019-06-03-d350fe1/bin/" + starexec_suffix
cvc4_binary = solvers_dir + "/releases/cvc4_master"

yices_comp_script = solvers_dir + "/comp/Yices_2.6.2/bin/" + starexec_suffix
yices_binary = solvers_dir + "/releases/yices-2.6.1/bin/yices-smt2" 

boolector_comp_script = solvers_dir + "/comp/Boolector/bin/" + starexec_suffix
boolector_binary = solvers_dir + "/releases/boolector/build/bin/boolector"

verit_comp_script = solvers_dir + "/comp/veriT/bin/" + starexec_suffix
verit_binary = solvers_dir + "/releases/veriT-stable2016/veriT" 

spasssatt_comp_script = solvers_dir + "/comp/SPASS-SATT/bin/" + starexec_suffix
spasssatt_binary = solvers_dir + "/releases/SPASS-SATT_v1.1/SPASS-SATT"

mathsat_comp_script = solvers_dir + "/comp/mathsat-20190601/bin/" + starexec_suffix + ".sh"
mathsat_binary = solvers_dir + "/releases/mathsat-5.5.4-linux-x86_64/bin/mathsat" 

z3_comp_script = solvers_dir + "/comp/z3-4.8.4-d6df51951f4c/bin/" + starexec_suffix
z3_binary = solvers_dir + "/releases/z3-4.8.5-x64-ubuntu-16.04/bin/z3" 
#ctrlergo_binary = solvers_dir + "/Ctrl-Ergo-2019/bin/" + starexec_suffix

#Commands are lists because they may include options
NAMES_AND_MODES_TO_COMMANDS =  {
    CVC4_NAME: {
        SOLVER_MODE.COMPETITION: [cvc4_comp_script],
        SOLVER_MODE.BINARY: [cvc4_binary],
        SOLVER_MODE.MODELS: [cvc4_binary, '--produce-models']
    },
    CVC4_FMF_NAME: {
        SOLVER_MODE.COMPETITION: None,
        SOLVER_MODE.BINARY: [cvc4_binary, '--finite-model-find'],
        SOLVER_MODE.MODELS: [cvc4_binary, '--produce-models', '--finite-model-find']
    },
    YICES_NAME: {
        SOLVER_MODE.COMPETITION: [yices_comp_script],
        SOLVER_MODE.BINARY: [yices_binary],
        SOLVER_MODE.MODELS: [yices_binary]
    },
    BOOLECTOR_NAME:  {
        SOLVER_MODE.COMPETITION: [boolector_comp_script],
        SOLVER_MODE.BINARY: [boolector_binary],
        SOLVER_MODE.MODELS: [boolector_binary, '--model-gen']
    },
    VERIT_NAME:  {
        SOLVER_MODE.COMPETITION: [verit_comp_script],
        SOLVER_MODE.BINARY: [verit_binary],
        SOLVER_MODE.MODELS: [verit_binary]
    },
    SPASSSATT_NAME:  {
        SOLVER_MODE.COMPETITION: [spasssatt_comp_script],
        SOLVER_MODE.BINARY: [spasssatt_binary],
        SOLVER_MODE.MODELS: [spasssatt_binary]
    },
    MATHSAT_NAME:  {
        SOLVER_MODE.COMPETITION: [mathsat_comp_script],
        SOLVER_MODE.BINARY: [mathsat_binary],
        SOLVER_MODE.MODELS: [mathsat_binary, '-model_generation=true']
    },
    Z3_NAME: {
        SOLVER_MODE.COMPETITION: [z3_comp_script],
        SOLVER_MODE.BINARY: [z3_binary],
        SOLVER_MODE.MODELS: [z3_binary]
    }
    #CTRLERGO_NAME: [ctrlergo_binary]
}

ALL_NAMES = list(NAMES_AND_MODES_TO_COMMANDS.keys())

def die(msg):
    print('error: {}'.format(msg))
    sys.exit(1)

def log(msg, config):
    if config.verbose:
        print('[dispatcher] {}'.format(msg))

# Spawn solver instance
def worker(i, solvers, procs, config):
    cmd = []
    cmd.extend(solvers[i])
    cmd.append(config.benchmark)
    try:
        log('{} start: {}'.format(i, ' '.join(cmd)), config)
        start = time.time()
        proc = subprocess.Popen(
                    cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        procs[i] = proc.pid

        stdout, stderr = proc.communicate()
        stdout_lines = stdout.decode('utf-8').splitlines()
        stderr_lines = stderr.decode('utf-8').splitlines()

        # Remove from process list since process terminated
        procs[i] = 0
        msg_lines = []
        if len(stdout_lines) > 0 :
            msg_lines.append(stdout_lines[0])
        msg_lines.extend(stderr_lines)
        log('{} done: {} ({}s)'.format(i, msg_lines, time.time() - start), config)
    except subprocess.CalledProcessError as error:
        log('{} error: {}'.format(i, error.output.strip()), config)
    except Exception as e:
        pass
    if is_result_sat_or_unsat(stdout_lines):
        return stdout_lines
    return ['unknown']

def is_result_sat_or_unsat(lines):
    return lines[0].strip() in ["sat", "unsat"]

# Terminate pool processes
def terminate(result):
    global g_result
    if not g_result and result[0] in ['sat', 'unsat']:
        g_result = result
        pool.terminate()

def parse_args():
    ncpus = multiprocessing.cpu_count()
    ap = argparse.ArgumentParser()
    ap.add_argument('-c', dest='ncpus', type=int, default=ncpus, help="number of CPUs to use (default: number of CPUs on machine)")
    ap.add_argument('-v', dest='verbose', action='store_true', help="increase verbosity")
    ap.add_argument('-e', dest='encoding', type=str, default="utf-8", help="system encoding (default: utf-8)")
    ap.add_argument('-s', dest='solvers', type=str, nargs='+', choices=ALL_NAMES + [NORMAL_NAME, GENERIC_NAME, ALL_NAME], help = "a space-separated list of solvers to use, or a special option (all, normal, generic).\n all - use all solvers. normal - select solver by benchmark. generic - use cvc4.")
    ap.add_argument('-m', dest='models', action='store_true', help = "should the solver run in model-producing mode?") 
    ap.add_argument('-o', dest='extra_options', type=str, nargs='*', help = "More options to use with the solver. This argument (unlike the others) must be given with an equal sign. For example: -o='--finite-model-find'")
    ap.add_argument('benchmark', help="path to smt-lib 2 file")
    return ap.parse_args()

def get_configs(args):
    config = Config()
    config.ncpus = args.ncpus
    config.verbose = args.verbose
    config.encoding = args.encoding
    config.solvers = args.solvers
    config.models = args.models
    config.extra_options = args.extra_options
    config.benchmark = args.benchmark
    return config

def get_solvers(config):
    input_solvers = config.solvers
    if input_solvers == None:
        result = select_solvers_by_bm(config)
    elif NORMAL_NAME in input_solvers: 
        #DEFAULT cannot be combined with any other solver
        assert(len(set(input_solvers)) == 1)
        result = select_solvers_by_bm(config)
    elif GENERIC_NAME in input_solvers:
        #GENERIC cannot be combined with any other solver
        assert(len(set(input_solvers)) == 1)
        result = select_solvers_by_names([CVC4_NAME], config)
    elif ALL_NAME in input_solvers:
        assert(len(set(input_solvers)) == 1)
        result = select_solvers_by_names(ALL_NAMES, config)
    else:
        assert(len(set(input_solvers)) >= 1)
        result = select_solvers_by_names(input_solvers, config)
    return result

def get_solver_mode(config):
    if config.models:
        return SOLVER_MODE.MODELS
    elif config.extra_options != None:
        return SOLVER_MODE.BINARY
    else:
        return SOLVER_MODE.COMPETITION

def get_extra_options(config):
    assert(config.solvers not in [NORMAL_NAME, ALL_NAME])
    if config.extra_options is None:
        return []
    else:
        return config.extra_options

def select_solvers_by_names(solver_names, config):
    solver_mode = get_solver_mode(config)
    extra_options = get_extra_options(config)
    return [get_solver_command(config, n, solver_mode, extra_options) for n in solver_names]

def select_solvers_by_bm(config):
    #get logic line
    bm_path = config.benchmark
    with open(bm_path, "r") as f:
        lines = f.read().splitlines()
    logic_lines = [l for l in lines if "set-logic" in l]
    assert(len(logic_lines) == 1)
    logic_line = logic_lines[0].lower()

    #get logic using regex
    p = re.compile('\\(set-logic\s*(.*)\s*\\)') 
    g = p.match(logic_line)
    logic = g.group(1)

    solver_names = select_solvers_by_logic(logic)
    return select_solvers_by_names(solver_names, config)

def select_solvers_by_logic(logic):
    logic = logic.upper()
    if "QF_" not in logic:
        result = [Z3_NAME, CVC4_NAME, VERIT_NAME]
    elif logic == "QF_LRA":
        result = [SPASSSATT_NAME, CVC4_NAME, YICES_NAME, VERIT_NAME]
    elif logic == "QF_LIA":
        result = [SPASSSATT_NAME, Z3_NAME, CVC4_NAME, YICES_NAME]
    elif logic == "QF_NIA":
            #Taking mathsat instead of approve
        result = [CVC4_NAME, YICES_NAME, Z3_NAME, MATHSAT_NAME]
    elif logic == "QF_NRA":
        result = [YICES_NAME, Z3_NAME, CVC4_NAME, MATHSAT_NAME]
    elif logic == "QF_AUFBV":
        result = [YICES_NAME, Z3_NAME, BOOLECTOR_NAME, CVC4_NAME]
    elif logic == "QF_ABV":
        result = [BOOLECTOR_NAME, YICES_NAME, CVC4_NAME, Z3_NAME]
    elif logic == "QF_UFBV":
        result = [YICES_NAME, BOOLECTOR_NAME, CVC4_NAME, Z3_NAME]
    elif logic == "QF_BV": 
        result = [BOOLECTOR_NAME, YICES_NAME, CVC4_NAME, Z3_NAME]
    elif logic == "QF_QUFLIA":
        result = [YICES_NAME, Z3_NAME, CVC4_NAME, VERIT_NAME]
    elif logic == "QF_AX":
        #missing smtinterpol and alt-ergo
        result = [YICES_NAME, Z3_NAME, CVC4_NAME]
    elif logic == "QF_AUFNIA":
        #missing alt ergo
        result = [MATHSAT_NAME, Z3_NAME, CVC4_NAME]
    elif logic in ["QF_ALIA", "QF_UFLIA"]:
        result = [YICES_NAME, CVC4_NAME, Z3_NAME, VERIT_NAME]
    elif logic in ["QF_S", "QF_SLIA"]:
        result = [CVC4_NAME]
    elif logic == "QF_ABVFP":
        result = [CVC4_NAME]
    elif logic == "QF_BVFP":
        result = [CVC4_NAME, Z3_NAME]
    elif logic == "QF_FP":
        #missing colibri
        result = [CVC4_NAME, Z3_NAME]
    else:
        assert(False)
    return result

def solve_configuration(config):
    #clean previous result
    global g_result
    g_result = None
    solvers = get_solvers(config)
    try:
        with multiprocessing.Manager() as manager:
            ncpus = min(len(solvers), config.ncpus)
            procs = manager.list([0 for i in range(ncpus)])

            log('starting {} solver instances.'.format(ncpus), config)
            global pool
            pool = multiprocessing.Pool(ncpus)
            for i in range(ncpus):
                pool.apply_async(worker, args=(i, solvers, procs, config), callback=terminate)
            pool.close()
            pool.join()

            # Kill remaining spawned solver processes
            for i in range(len(procs)):
                pid = procs[i]
                if pid == 0:
                    continue
                try:
                    os.kill(pid, signal.SIGKILL)
                    log('killed {} ({})'.format(i, pid), config)
                except OSError:
                    log('could not kill: {}'.format(pid), config)
    except:
        pass

    if g_result:
        return g_result
    else:
        return ['unknown']

if __name__ == '__main__':
    args = parse_args()
    config = get_configs(args)
    if not config.verbose:
        signal.signal(signal.SIGINT, lambda x, y: sys.exit(0))
    result = solve_configuration(config)
    print("\n".join(result))
