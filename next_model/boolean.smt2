(set-logic QF_UF)
(declare-fun B () Bool)
(declare-fun C () Bool)
(declare-fun D () Bool)

(assert (or B C D))

(check-sat)
(get-model)

(check-sat)
(get-model)

(check-sat)
(get-model)

(check-sat)
(get-model)

(check-sat)
(get-model)
