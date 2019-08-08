(set-logic QF_BV)     
(declare-fun a () (_ BitVec 4)) 
(declare-fun b () (_ BitVec 4)) 
(assert (bvugt a b))       
(assert (bvugt b (_ bv0 4)))       
(assert (= a (bvmul (_ bv2 4) b))) 
(check-sat)            
(get-value (a b))      
                       
