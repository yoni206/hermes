(set-logic QF_UFNRA)
(declare-sort S 0)
(declare-fun f (S) Real)
(declare-const s S)
(declare-const t S)
(assert (= (f s) (f t))) 
(check-sat)
