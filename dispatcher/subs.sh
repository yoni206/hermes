#!/bin/bash
DIR=`pwd`
SOLVERS_DIR=$DIR/solvers
sed -i "s|./boolector|$SOLVERS_DIR/Boolector/bin/./boolector|" $SOLVERS_DIR/Boolector/bin/starexec_run_default
sed -i "s|./cvc4|$SOLVERS_DIR/CVC4-2019-06-03-d350fe1/bin/./cvc4|" $SOLVERS_DIR/CVC4-2019-06-03-d350fe1/bin/starexec_run_default
sed -i "s|./run|$SOLVERS_DIR/Ctrl-Ergo-2019/bin/./run|" $SOLVERS_DIR/Ctrl-Ergo-2019/bin/starexec_run_default
sed -i "s|./SPASS_SATT|$SOLVERS_DIR/SPASS-SATT/bin/./SPASS-SATT|" $SOLVERS_DIR/SPASS-SATT/bin/starexec_run_default
sed -i "s|./yices2|$SOLVERS_DIR/Yices_2.6.2/bin/./yices2|" $SOLVERS_DIR/Yices_2.6.2/bin/starexec_run_default
sed -i "s|./mathsat|$SOLVERS_DIR/mathsat-20190601/bin/./mathsat|" $SOLVERS_DIR/mathsat-20190601/bin/starexec_run_default
sed -i "s|./veriT|$SOLVERS_DIR/veriT/bin/./veriT|" $SOLVERS_DIR/veriT/bin/starexec_run_default
sed -i "s|./z3|$SOLVERS_DIR/z3-4.8.4-d6df51951f4c/bin/./z3|" $SOLVERS_DIR/z3-4.8.4-d6df51951f4c/bin/starexec_run_default
