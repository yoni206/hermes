(set-logic UFNIA)
(declare-fun a () Int)
(declare-fun b () Int)
(declare-fun f (Int) Int)

(assert (= (+ a a) b))
;(assert (> (f a) (f b)))
(assert (<= (f a) (f b)))

(check-sat)
(get-value (a b (f a) (f b)))

(check-sat)
(get-value (a b (f a) (f b) ))


(check-sat)
(get-value (a b (f a) (f b)))


(check-sat)
(get-value (a b (f a) (f b)))
(get-value (a))

(check-sat)
(get-value (a b (f a) (f b)))
