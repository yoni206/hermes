(set-logic QF_NRA)
(declare-fun ack29 () Real )
(declare-fun ack18 () Int )
(declare-fun ack19 () Real )
(declare-fun FV9 () Int )
(declare-fun FV10 () Int )
(declare-fun ack20 () Real )
(declare-fun ack21__pure () Real )
(declare-fun ack24__pure () Real )
(declare-fun ack27__pure () Real )
(declare-fun ack23 () Real )
(declare-fun ack22 () Real )
(declare-fun ack12 () Real )
(declare-fun ack25 () Real )
(declare-fun ack26 () Real )
(declare-fun ack14 () Real )
(declare-fun ack15 () Real )
(declare-fun ack16 () Real )
(declare-fun ack17 () Real )
(declare-fun ack28 () Real )
(assert (and (and (and (=> (= ack24__pure ack21__pure) (= ack26 ack23)) (=> (= ack24__pure ack27__pure) (= ack26 ack29)) (=> (= ack21__pure ack27__pure) (= ack23 ack29)) (=> (= ack24__pure ack21__pure) (= ack25 ack22)) (=> (= ack24__pure ack27__pure) (= ack25 ack28)) (=> (= ack21__pure ack27__pure) (= ack22 ack28))) (and (and (or (not (and (= ack29 ack20) (= ack28 ack16))) true) (or (not true) (and (= ack29 ack20) (= ack28 ack16)))) (and (or (not (= ack29 ack28)) true) (or (not true) (= ack29 ack28))) (and (or (not (and (= ack26 ack19) (= ack25 ack15))) true) (or (not true) (and (= ack26 ack19) (= ack25 ack15)))) (and (or (not (= ack26 ack25)) true) (or (not true) (= ack26 ack25))) (and (or (not (and (= ack23 ack17) (= ack22 ack12))) true) (or (not true) (and (= ack23 ack17) (= ack22 ack12)))) (and (or (not (= ack23 ack22)) true) (or (not true) (= ack23 ack22))) (and (and (<= 1 ack18) (and (and (and (and (<= 0 FV10) (<= FV10 ack18)) (<= 1 FV9)) (<= FV9 ack18)) (and (or (= ack20 (/ (* 1  FV9) (* 1  ack18))) (= ack20 (/ (* 1  (* (- 1) FV9)) (* 1  ack18)))) (or (= ack19 (/ (* 1  FV10) (* 1  ack18))) (= ack19 (/ (* 1  (* (- 1) FV10)) (* 1  ack18))))))) (or (not (and (or (= ack16 1.0) (= ack16 (- 1.0))) (or (or (= ack15 0.0) (= ack15 1.0)) (= ack15 (- 1.0))))) (= ack17 (+ (* (* ack16 (/ 6369051672525773 4503599627370496)) (sin ack14)) (* (* ack15 (/ 6369051672525773 4503599627370496)) (cos ack14)))))) (not (and (<= ack12 1.0) (<= (- 1.0) ack12))))) true) )
(check-sat)