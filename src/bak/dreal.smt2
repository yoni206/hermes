(set-logic QF_NRA)
(declare-fun FV9 () Int )
(declare-fun FV10 () Int )
(declare-fun __x0__ () Real )
(declare-fun __x2__ () Real )
(declare-fun __x3__ () Real )
(declare-fun __x4__ () hermes.iml.aadl.Connection_Real )
(declare-fun __x5__ () Real )
(declare-fun __x6__ () Real )
(declare-fun __x7__ () hermes.iml.aadl.Connection_Real )
(declare-fun __x8__ () Real )
(declare-fun __x9__ () Real )
(declare-fun __x11__ () Real )
(declare-fun __x13__ () Real )
(declare-fun __x14__ () Real )
(declare-fun __x15__ () Real )
(declare-fun __x16__ () Real )
(declare-fun __x17__ () Real )
(declare-fun __x18__ () Int )
(assert (and (and (=> (= __x7__ __x4__) (= __x8__ __x5__)) (=> (= __x7__ __x4__) (= __x6__ __x3__))) (and (and (or (not (= __x0__ __x2__)) true) (or (not true) (= __x0__ __x2__))) (and (or (not (= __x3__ __x5__)) true) (or (not true) (= __x3__ __x5__))) (and (or (not (= __x6__ __x8__)) true) (or (not true) (= __x6__ __x8__))) (and (or (not (and (= __x6__ __x9__) (= __x8__ __x11__))) true) (or (not true) (and (= __x6__ __x9__) (= __x8__ __x11__)))) (and (or (not (and (= __x0__ __x13__) (= __x2__ __x14__))) true) (or (not true) (and (= __x0__ __x13__) (= __x2__ __x14__)))) (and (or (not (and (= __x3__ __x15__) (= __x5__ __x16__))) true) (or (not true) (and (= __x3__ __x15__) (= __x5__ __x16__)))) (and (or (not (and (or (= __x14__ 1.0) (= __x14__ (- 1.0))) (or (= __x16__ 0.0) (= __x16__ 1.0) (= __x16__ (- 1.0))))) (= __x9__ (+ (* __x14__ (/ 6369051672525773 4503599627370496) (sin __x17__)) (* __x16__ (/ 6369051672525773 4503599627370496) (cos __x17__))))) (and (<= 1 __x18__) (and (and (<= 1 FV10) (<= FV10 __x18__) (<= 1 FV9) (<= FV9 __x18__)) (and (or (= __x13__ (/ (* 1  FV9) (* 1  __x18__))) (= __x13__ (* (- 1.0) (/ (* 1  FV9) (* 1  __x18__))))) (or (= __x15__ (* 1  (/ FV10 __x18__))) (= __x15__ (* (- 1.0) (* 1  (/ FV10 __x18__))))))))) (not (and (<= __x11__ 1.0) (<= 1.0 __x11__))))) )
(check-sat)