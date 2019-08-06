#based on https://github.com/Boolector/boolector/blob/smtcomp19/contrib/poolector.py
import argparse
import multiprocessing
import subprocess
import sys
import time
import signal
import os
import re

g_result = None
script_dir = os.path.dirname(os.path.realpath(__file__))
solvers_dir = script_dir + "/solvers"
starexec_suffix = "starexec_run_default"


CVC4_NAME = "cvc4"
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


cvc4_binary = solvers_dir + "/CVC4-2019-06-03-d350fe1/bin/" + starexec_suffix
yices_binary = solvers_dir + "/Yices_2.6.2/bin/" + starexec_suffix
boolector_binary = solvers_dir + "/Boolector/bin/" + starexec_suffix
verit_binary = solvers_dir + "/veriT/bin/" + starexec_suffix
spasssatt_binary = solvers_dir + "/SPASS-SATT/bin/" + starexec_suffix
mathsat_binary = solvers_dir + "/mathsat-20190601/bin/" + starexec_suffix + ".sh"
z3_binary = solvers_dir + "/z3-4.8.4-d6df51951f4c/bin/" + starexec_suffix
#ctrlergo_binary = solvers_dir + "/Ctrl-Ergo-2019/bin/" + starexec_suffix

#Commands are lists because they may include options
NAMES_TO_COMMANDS =  {
    CVC4_NAME: [cvc4_binary],
    YICES_NAME: [yices_binary],
    BOOLECTOR_NAME: [boolector_binary],
    VERIT_NAME: [verit_binary],
    SPASSSATT_NAME: [spasssatt_binary],
    MATHSAT_NAME: [mathsat_binary],
    Z3_NAME: [z3_binary],
    #CTRLERGO_NAME: [ctrlergo_binary]
}

ALL_NAMES = list(NAMES_TO_COMMANDS.keys())

def die(msg):
    print('error: {}'.format(msg))
    sys.exit(1)

def log(msg):
    if args.verbose:
        print('[dispatcher] {}'.format(msg))

# Spawn solver instance
def worker(i, procs):
    cmd = []
    cmd.extend(solvers[i])
    cmd.append(args.benchmark)

    result = 'unknown'
    try:
        log('{} start: {}'.format(i, ' '.join(cmd)))
        start = time.time()
        proc = subprocess.Popen(
                    cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        procs[i] = proc.pid

        stdout, stderr = proc.communicate()
        encoding = args.encoding
        result = ''.join([stdout.decode(encoding), stderr.decode(encoding)]).strip()

        # Remove from process list since process terminated
        procs[i] = 0

        log('{} done: {} ({}s)'.format(i, result, time.time() - start))
    except subprocess.CalledProcessError as error:
        log('{} error: {}'.format(i, error.output.strip()))
    except:
        pass

    if result in ['sat', 'unsat']:
        return result
    return 'unknown'

# Terminate pool processes
def terminate(result):
    global g_result
    if not g_result and result in ['sat', 'unsat']:
        g_result = result
        pool.terminate()

def parse_args():
    ncpus = multiprocessing.cpu_count()
    ap = argparse.ArgumentParser()
    ap.add_argument('-c', dest='ncpus', type=int, default=ncpus, help="number of CPUs to use (default: number of CPUs on machine)")
    ap.add_argument('-v', dest='verbose', action='store_true', help="increase verbosity")
    ap.add_argument('-e', dest='encoding', type=str, default="utf-8", help="system encoding (default: utf-8)")
    ap.add_argument('-s', dest='solvers', type=str, nargs='+', choices=ALL_NAMES + [NORMAL_NAME, GENERIC_NAME, ALL_NAME], help = "a space-separated list of solvers to use, or a special option (all, normal, generic).\n all - use all solvers. normal - select solver by benchmark. generic - use cvc4.")
    ap.add_argument('benchmark', help="path to smt-lib 2 file")
    return ap.parse_args()

def get_solvers():
    input_solvers = args.solvers
    if input_solvers == None:
        result = select_solvers_by_bm()
    elif NORMAL_NAME in input_solvers: 
        #DEFAULT cannot be combined with any other solver
        assert(len(set(input_solvers)) == 1)
        result = select_solvers_by_bm()
    elif GENERIC_NAME in input_solvers:
        #GENERIC cannot be combined with any other solver
        assert(len(set(input_solvers)) == 1)
        result = select_solvers_by_names([CVC4_NAME])
    elif ALL_NAME in input_solvers:
        assert(len(set(input_solvers)) == 1)
        result = select_solvers_by_names(ALL_NAMES)
    else:
        assert(len(set(input_solvers)) >= 1)
        result = select_solvers_by_names(input_solvers)
    return result

def select_solvers_by_names(solver_names):
    return [NAMES_TO_COMMANDS[n] for n in solver_names]

def select_solvers_by_bm():
    #get logic line
    bm_path = args.benchmark
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
    return select_solvers_by_names(solver_names)

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
    elif logic == "QF_ALIA":
        result = [YICES_NAME, CVC4_NAME, Z3_NAME, VERIT]
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


if __name__ == '__main__':
    args = parse_args()
    solvers = get_solvers()
    try:
        with multiprocessing.Manager() as manager:
            ncpus = min(len(solvers), args.ncpus)
            procs = manager.list([0 for i in range(ncpus)])

            log('starting {} solver instances.'.format(ncpus))
            pool = multiprocessing.Pool(ncpus)
            for i in range(ncpus):
                pool.apply_async(worker, args=(i, procs), callback=terminate)
            pool.close()
            pool.join()

            # Kill remaining spawned solver processes
            for i in range(len(procs)):
                pid = procs[i]
                if pid == 0:
                    continue
                try:
                    os.kill(pid, signal.SIGKILL)
                    log('killed {} ({})'.format(i, pid))
                except OSError:
                    log('could not kill: {}'.format(pid))
    except:
        pass

    if g_result:
        print(g_result)
    else:
        print('unknown')
