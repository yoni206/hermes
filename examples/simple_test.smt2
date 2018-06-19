(assert (forall ((y Int)) (= y y)))
(assert (forall ((y Real)) (= y y)))

(define-fun f ((n Int)) Int (+ n n))
(define-fun g ((n Real)) Real (+ n n))
(declare-const x Int)
(assert (= (f x) (+ x 1)))
(assert (= (g x) (+ (f x) 1)))


(check-sat)
