## Prerequisites: 
  - docker

## Description
  - This image contains a script "dispatcher.py" that runs SMT-LIB 2 files using various solvers.
  - The script runs in two modes:
    - normal: running the query using a portfolio of solvers. 
              The solvers are chosen based on the results
              of the last SMT-COMP.
              Roughly speaking, the best 4 solvers for the logic of the query are used.
              The current pool of solvers includes:
              CVC4, Z3, Yices, VERIT, MATHSAT, SPASS_SATT
    - generic: running the query using CVC4

## Installation:
  - cd to the main directory (the directory that contains the current README file)
  - run:  
    `# docker build -t dispatcher .`

## Usage:
### As server:
  - `# docker run -it --rm -p 5000:5000 dispatcher bash run_server.sh`

### As standalone solver:
  - run the following command:  
    `# docker run -v <absolute_path>:/smt_files/ -it dispatcher python3 dispatcher.py /smt_files/<filename> -s <mode>`  
    where:
      - `<filename>` is the name to an smt2 file in <absolute_path>
      - `<mode>` is either "normal" (for running a portfolio) or "generic" (for running CVC4)

Example:
  - The following run will return a result quickly:  
    `# docker run -v <absolute_path-to-main-dir>/dispatcher/examples/smtlib:/smt_files/ -it dispatcher python3 dispatcher.py /smt_files/term-UCZhjg.smt2 -s normal`  
  - The following run will take long time (few minutes) before terminating:  
    `# docker run -v <absolute_path-to-main-dir>/dispatcher/examples/smtlib:/smt_files/ -it dispatcher python3 dispatcher.py /smt_files/term-UCZhjg.smt2 -s generic`  

Additional Options:
- Using the -s option, `<mode>` can have more values than "generic" or "normal". 
  It can be a space-separated list of solver names, to be used in portfolio.
- Using -v will dump some debug details
