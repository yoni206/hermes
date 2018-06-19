(set-logic ALL)
(declare-const i Int)
(declare-const r Real)
(assert (= (to_real i) r))
(check-sat)

