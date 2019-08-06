#!/bin/bash
DIR=`pwd`
SOLVERS_DIR=$DIR/solvers
sed -i "s|./boolector|$SOLVERS_DIR/Boolector/bin/./boolector|" $SOLVERS_DIR/Boolector/bin/starexec_run_default
sed -i "s|./cvc4|$SOLVERS_DIR/CVC4-2019-06-03-d350fe1/bin/./cvc4|" $SOLVERS_DIR/CVC4-2019-06-03-d350fe1/bin/starexec_run_default
