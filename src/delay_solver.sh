#!/bin/bash
java -jar $DELAY_SOLVER_DIR/com.utc.utrc.hermes.dst.delayanalysis.jar $1 tmp.tmp
cat tmp.tmp
rm tmp.tmp
