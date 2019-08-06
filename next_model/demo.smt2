(set-logic QF_NIA)
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun z () Int)

(define-fun A () Bool (distinct x y))
(define-fun B () Bool (= (* x x) (* y y)))
(define-fun C () Bool (= (* y y) (* z z)))
(define-fun D () Bool (= (* x x) (* z z)))

(assert (and A (or B C D)))

(check-sat)
(get-model)
(get-value (A B C D))

(check-sat)
(get-model)
(get-value (A B C D))

(check-sat)
(get-model)
(get-value (A B C D))

(check-sat)
(get-model)
(get-value (A B C D))

(check-sat)
(get-model)
(get-value (A B C D))
