(set-logic ALL)
(declare-sort hermes.iml.aadl.Connection<Float> 0)
(declare-fun ack21 () Real )
(declare-fun ack22 () Real )
(declare-fun ack23 () hermes.iml.aadl.Connection<Float> )
(declare-fun ack24 () Real )
(declare-fun ack25 () Real )
(declare-fun ack12 () Real )
(declare-fun ack26 () hermes.iml.aadl.Connection<Float> )
(declare-fun ack27 () Real )
(declare-fun ack28 () Real )
(declare-fun ack13 () Real )
(declare-fun ack15 () Int )
(declare-fun ack16 () Real )
(declare-fun ack17 () Real )
(declare-fun FV9 () Int )
(declare-fun FV10 () Int )
(declare-fun ack18 () hermes.iml.aadl.Connection<Float> )
(declare-fun ack19 () Real )
(declare-fun ack20 () Real )
(assert (and 

;consistency lemmas
;(and (=> (= ack23 ack26) (= ack25 ack28)) (=> (= ack18 ack26) (= ack20 ack28)) (=> (= ack23 ack18) (= ack24 ack19)) (=> (= ack23 ack26) (= ack24 ack27)) (=> (= ack18 ack26) (= ack19 ack27)) (=> (= ack23 ack18) (= ack25 ack20)))

;Alessandro's disequalities
(distinct ack18 ack23 ack26)

;Original query (after ackermannization)
 (and (and (or (not (and (= ack28 ack17) (= ack27 ack13))) true) (or (not true) (and (= ack28 ack17) (= ack27 ack13)))) (and (or (not (= ack28 ack27)) true) (or (not true) (= ack28 ack27))) (and (or (not (and (= ack25 ack16) (= ack24 ack12))) true) (or (not true) (and (= ack25 ack16) (= ack24 ack12)))) (and (or (not (= ack25 ack24)) true) (or (not true) (= ack25 ack24))) (and (or (not (and (= ack20 ack22) (= ack19 ack21))) true) (or (not true) (and (= ack20 ack22) (= ack19 ack21)))) (and (or (not (= ack20 ack19)) true) (or (not true) (= ack20 ack19))) (and (<= 1 ack15) (and (and (and (and (<= 0 FV10) (<= FV10 ack15)) (<= 1 FV9)) (<= FV9 ack15)) (and (or (= ack17 (/ (to_real FV9) (to_real ack15))) (= ack17 (/ (to_real (* (- 1) FV9)) (to_real ack15)))) (or (= ack16 (/ (to_real FV10) (to_real ack15))) (= ack16 (/ (to_real (* (- 1) FV10)) (to_real ack15))))))) (not (and (or (= ack13 1.0) (= ack13 (- 1.0))) (or (or (= ack12 0.0) (= ack12 1.0)) (= ack12 (- 1.0))))))) )
(check-sat)
(get-model)
