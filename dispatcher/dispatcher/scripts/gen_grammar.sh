THIS_DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"
SMTLIB_DIR=`realpath $THIS_DIR/../examples/`
SYGUS_FILE=$SMTLIB_DIR/grammar.sy
PATTERNS="p.recv_map__data__ p.RADIO__send_status_out__data__ p.RADIO__recv_map_out__data__ p.FPLN__flight_plan__data__ p.WPM__waypoint__data__ p.UART__position_status_out__data__ p.UART__waypoint_out__data__ p.position_status__data__"

#clean file
echo "" > $SYGUS_FILE

#grammar prefix
echo "((GA Bool) (GI Int))" >> $SYGUS_FILE
echo "(" >> $SYGUS_FILE

#grammar for Bool
echo "(GA Bool (" >> $SYGUS_FILE
echo "  (= GI GI)" >> $SYGUS_FILE

#boolean variables in the grammar
for val in $PATTERNS; do
  cat $SMTLIB_DIR/Assessment2/Assessment3_test1_flattenQ1.smt2 | grep "declare.*$val" | grep Bool | cut -d' ' -f2 | sed 's/^/  /g' >> $SYGUS_FILE
done

#end of boolean variables list
echo "))" >> $SYGUS_FILE

#grammar for int
echo "(GI Int (" >> $SYGUS_FILE
echo "  (+ GI GI) (- GI) 0 1" >> $SYGUS_FILE

#list of int vars
for val in $PATTERNS; do
  cat $SMTLIB_DIR/Assessment2/Assessment3_test1_flattenQ1.smt2 | grep "declare.*$val" | grep Int| cut -d' ' -f2 | sed 's/^/  /g' >> $SYGUS_FILE
done

#end of int vars list
echo ")" >> $SYGUS_FILE

#end of int grammar
echo ")" >> $SYGUS_FILE



#end of sygus grammar
echo ")" >> $SYGUS_FILE
