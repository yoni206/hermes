; COMMAND-LINE: --incremental
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
; EXPECT: unsat
; EXPECT: sat
(set-logic QF_LIA)
(declare-fun x0 () Bool)
(declare-fun x1 () Bool)
(declare-fun x2 () Bool)
(declare-fun x3 () Bool)
(assert (not (and (not (and (or (not (or (not x0) (or x2 x2))) (or (or (or x2 x1) (or x1 x3)) (not (or x3 x2)))) (or (not (not (and x1 x2))) (and (not (not x2)) (and (or x0 x2) (or x0 x1)))))) (not (not (or (or (and (or x0 x1) (not x3)) (and (or x3 x3) (and x3 x1))) (not (or (or x0 x2) (or x2 x3)))))))))
(assert (and (not (and (and (not (not (not x2))) (and (or (or x3 x0) (not x1)) (and (or x0 x0) (and x1 x1)))) (and (and (and (and x0 x3) (and x2 x1)) (or (not x3) (not x0))) (not (and (and x2 x0) (and x2 x1)))))) (and (or (or (and (not (or x0 x1)) (not (and x2 x3))) (and (not (not x0)) (or (or x3 x1) (or x1 x2)))) (or (or (or (not x0) (and x0 x1)) (and (and x2 x2) (or x3 x3))) (or (not (or x1 x1)) (and (and x0 x3) (and x3 x2))))) (or (not (not (not (and x3 x1)))) (or (and (not (and x0 x2)) (not (or x0 x1))) (and (not (and x3 x3)) (not (not x1))))))))
(assert (not (and x0 x3)))
(check-sat)
