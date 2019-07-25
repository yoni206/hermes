(set-logic QF_LIA)
(declare-fun a () Int)
(declare-fun b () Int)
(declare-fun c () Int)

(assert (or (distinct a b) (distinct a c)))

(check-sat)
(get-model)
(check-sat)
(get-model)
(check-sat)
(get-model)
(check-sat)
(get-model)

