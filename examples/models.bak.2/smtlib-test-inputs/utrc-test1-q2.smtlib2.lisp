(declare-sort hermes.iml.aadl.Connection_Real)
(declare-fun hermes.iml.aadl.Connection_Real.source (hermes.iml.aadl.Connection_Real) Real) 
(declare-fun hermes.iml.aadl.Connection_Real.target (hermes.iml.aadl.Connection_Real) Real) 
(define-fun hermes.iml.aadl.Connection_Real.a1 (x!1 hermes.iml.aadl.Connection_Real) Bool
	(= (hermes.iml.aadl.Connection_Real.source x!1) (hermes.iml.aadl.Connection_Real.target x!1))
)


(declare-sort utrc.test1.S1)
(declare-fun utrc.test1.S1.i1 (S1) Real)
(declare-fun utrc.test1.S1.i2 (S1) Real)
(declare-fun utrc.test1.S1.o1 (S1) Real)
(declare-fun utrc.test1.S1.n (S1) Int)
(define-fun utrc.test1.S1.a1 (x!1 S1) Bool 
	(exists ((x Int)(y Int)) 
		(and
			(and  
				(>= y 0)
				(<= y n)
				(>= x 1)
				(<= x 0)
			)
			(and   
				(or 
					(= (utrc.test1.S1.i1 x!1) (/ x n))
					(= (utrc.test1.S1.i1 x!1) (* -1 (/ x n)))
				)
				(or 
					(= (utrc.test1.S1.i2 x!1) (/ y n))
					(= (utrc.test1.S1.i2 x!1) (* -1 (/ y n)))
				)
			)
		)
	)
)

(define-fun utrc.test1.S1.g1 (x!1 S1) Bool
	(and (<= (utrc.test1.S1.o1 x!1) 1) 
		 (>= (utrc.test1.S1.o1 x!1) 1)
	)
)

(declare-sort utrc.test1.S2)
(declare-fun utrc.test1.S2.i1 (S2) Real)
(declare-fun utrc.test1.S2.i2 (S2) Real)
(declare-fun utrc.test1.S2.o1 (S2) Real)
(declare-fun utrc.test1.S2.alpha (S2) Real)
(define-fun utrc.test1.S2.a1 (x!1 S2) Bool 
	(and   
		(or 
			(= (utrc.test1.S2.i1 x!1) 1)
			(= (utrc.test1.S2.i1 x!1) -1)
		)
		(or 
			(= (utrc.test1.S2.i2 x!1) 0)
			(= (utrc.test1.S2.i2 x!1) 1)
			(= (utrc.test1.S2.i2 x!1) -1)
		)
	)
)

(define-fun utrc.test1.S2.g1 (x!1 S2) Bool
	(= (utrc.test1.S2.o1 x!1) 
		(+
			(* 
				(utrc.test1.S2.i1 x!1)
				(sqrt 2)
				(sin utrc.test1.S2.alpha x!1)
			)
			(*
				(utrc.test1.S2.i2 x!1)
				(sqrt 2)
				(cos utrc.test1.S2.alpha x!1)
			)
		)	
	) 
)

(declare-sort utrc.test1.S1__impl)
(declare-fun utrc.test1.S1__impl.S2_sub (S1__impl) S2)
(declare-fun utrc.test1.S1__impl.base_0 (S1__impl) S1)

(declare-fun utrc.test1.S1__impl.i1_TO_A (S1_impl) hermes.iml.aadl.Connection_Real)
(define-fun utrc.test1.S1__impl.i1_TO_A.init (x!1 S1_imp) Bool
	(and 
		(= (hermes.iml.aadl.Connection_Real.source (utrc.test1.S1__impl.i1_TO_A x!1))  
		   (utrc.test1.S1.i1 (utrc.test1.S1__impl.base_0 x!1))
		)  
		(= (hermes.iml.aadl.Connection_Real.target (utrc.test1.S1__impl.i1_TO_A x!1))  
		   (utrc.test1.S2.i1 (utrc.test1.S1__impl.S2_sub x!1))
		)
	)
)

(declare-fun utrc.test1.S1__impl.i2_TO_A (S1_impl) hermes.iml.aadl.Connection_Real)
(define-fun utrc.test1.S1__impl.i2_TO_A.init (x!1 S1_imp) Bool
	(and 
		(= (hermes.iml.aadl.Connection_Real.source (utrc.test1.S1__impl.i2_TO_A x!1))  
		   (utrc.test1.S1.i2 (utrc.test1.S1__impl.base_0 x!1))
		)  
		(= (hermes.iml.aadl.Connection_Real.target (utrc.test1.S1__impl.i2_TO_A x!1))  
		   (utrc.test1.S2.i2 (utrc.test1.S1__impl.S2_sub x!1))
		)
	)
)

(declare-fun utrc.test1.S1__impl.S2_TO_o1 (S1_impl) hermes.iml.aadl.Connection_Real)
(define-fun utrc.test1.S1__impl.S2_TO_o1.init (x!1 S1_imp) Bool
	(and 
		(= (hermes.iml.aadl.Connection_Real.source (utrc.test1.S1__impl.S2_TO_o1 x!1))  
		   (utrc.test1.S2.o1 (utrc.test1.S1__impl.S2_sub x!1))
		)  
		(= (hermes.iml.aadl.Connection_Real.target (utrc.test1.S1__impl.S2_TO_o1 x!1))  
		   (utrc.test1.S1.o1 (utrc.test1.S1__impl.base_0 x!1))
		)
	)
)


(declare-fun inst () S1_impl)
;; Assert all that needs to be asserted
(assert 
	(= (hermes.iml.aadl.Connection_Real.a1 (utrc.test1.S1__impl.i1_TO_A inst)) true)
)
(assert 
	(= (hermes.iml.aadl.Connection_Real.a1 (utrc.test1.S1__impl.i2_TO_A inst)) true)
)
(assert 
	(= (hermes.iml.aadl.Connection_Real.a1 (utrc.test1.S1__impl.S2_TO_o1 inst)) true)
)
(assert 
	(= (utrc.test1.S1__impl.S2_TO_o1.init inst) true)
)
(assert 
	(= (utrc.test1.S1__impl.i1_TO_A.init inst) true)
)
(assert 
	(= (utrc.test1.S1__impl.i2_TO_A.init inst) true)
)

(assert 
	(and 
		(utrc.test1.S1.a1 (utrc.test1.S1__impl.base_0 inst))
		(not (utrc.test1.S2.a1 (utrc.test1.S1__impl.S2_sub inst)))
	)
)


