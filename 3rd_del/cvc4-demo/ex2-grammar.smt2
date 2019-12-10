(set-logic QF_LIA)
(set-option :produce-abducts true)

(declare-fun n () Int)
(declare-fun m () Int)
(declare-fun i () Int)
(declare-fun j () Int)

(assert (and (>= n 0) (>= m 0)))
(assert (< n i))
(assert (< (+ i j) m))

(get-abduct A 
  (<= n m)
  ((GA Bool) (GI Int))
  (
  (GA Bool ((>= GI GI)))
  (GI Int ((+ GI GI) (- GI) j i 0 1))
  )
)
