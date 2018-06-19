(declare-const a (_ BitVec 32))
(declare-const b (_ BitVec 32))
(declare-const c (_ BitVec 32))
(declare-const d (_ BitVec 32))
(declare-const e (_ BitVec 32))

(assert (or (= a b) (= a c) (= a d) (= a e)))

(assert (not (= a b)))
(assert (not (= a c)))
(assert (not (= a d)))
(assert (not (= a e)))



(declare-fun n () Real)
(declare-fun x () Real)

; This example is to exercise the model builder with unknown results

(assert (>= n 1))
(assert (<= n 1))
(assert (<= x 1))
(assert (>= x 1))
(assert (not (= (+ x n) 1)))
(check-sat)

