(graph test1

	(node entailment n1)
	(node entailment n2)
	(node and n3)
	(node done n4)

	(edge e1 __ n1.kb 
		(smt25 
			(
				(declare-sort hermes.iml.aadl.Connection_Real 0)
				(declare-fun hermes.iml.aadl.Connection_Real.source (hermes.iml.aadl.Connection_Real) Real) 
				(declare-fun hermes.iml.aadl.Connection_Real.target (hermes.iml.aadl.Connection_Real) Real) 
				(define-fun hermes.iml.aadl.Connection_Real.a1 ((x!1 hermes.iml.aadl.Connection_Real)) Bool
					(= (hermes.iml.aadl.Connection_Real.source x!1) (hermes.iml.aadl.Connection_Real.target x!1))
				)

                (declare-const r1 Real)
                (assert (= r1 0))
				(declare-sort utrc.test1.S1 0)
				(declare-fun utrc.test1.S1.i1 (utrc.test1.S1) Real)
				(declare-fun utrc.test1.S1.i2 (utrc.test1.S1) Real)
				(declare-fun utrc.test1.S1.o1 (utrc.test1.S1) Real)
				(declare-fun utrc.test1.S1.n (utrc.test1.S1) Int)
				(define-fun utrc.test1.S1.a1 ((x!1 utrc.test1.S1)) Bool 
					(and
						(>= (utrc.test1.S1.n x!1) 1)  
						(exists ((x Int)(y Int)) 
							(and
								(and  
									(>= y 1)
									(<= y (utrc.test1.S1.n x!1))
									(>= x 1)
									(<= x (utrc.test1.S1.n x!1))
								)
								(and   
									(or 
										(= (utrc.test1.S1.i1 x!1) (to_real (/ x (utrc.test1.S1.n x!1))))
										(= (utrc.test1.S1.i1 x!1) (* -1 (to_real (/ x (utrc.test1.S1.n x!1))))
									))
									(or 
										(= (utrc.test1.S1.i2 x!1) (to_real (/ y (utrc.test1.S1.n x!1))))
										(= (utrc.test1.S1.i2 x!1) (* -1 (to_real (/ y (utrc.test1.S1.n x!1)))))
									)
								)
							)
						)
					)
				)

				(define-fun utrc.test1.S1.g1 ((x!1 utrc.test1.S1)) Bool
					(and (<= (utrc.test1.S1.o1 x!1) 1) 
						 (>= (utrc.test1.S1.o1 x!1) 1)
					)
				)

				(declare-sort utrc.test1.S2 0)
				(declare-fun utrc.test1.S2.i1 (utrc.test1.S2) Real)
				(declare-fun utrc.test1.S2.i2 (utrc.test1.S2) Real)
				(declare-fun utrc.test1.S2.o1 (utrc.test1.S2) Real)
				(declare-fun utrc.test1.S2.alpha (utrc.test1.S2) Real)
				(define-fun utrc.test1.S2.a1 ((x!1 utrc.test1.S2)) Bool 
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

				(define-fun utrc.test1.S2.g1 ((x!1 utrc.test1.S2)) Bool
					(= (utrc.test1.S2.o1 x!1) 
						(+
							(* 
								(utrc.test1.S2.i1 x!1)
								(pow (to_real 2) 0.5)
								;(sin (utrc.test1.S2.alpha x!1))
							)
							(*
								(utrc.test1.S2.i2 x!1)
								(pow (to_real 2) 0.5)
								;(cos (utrc.test1.S2.alpha x!1))
							)
						)	
					) 
				)

				(declare-sort utrc.test1.S1__impl 0)
				(declare-fun utrc.test1.S1__impl.S2_sub (utrc.test1.S1__impl) utrc.test1.S2)
				(declare-fun utrc.test1.S1__impl.base_0 (utrc.test1.S1__impl) utrc.test1.S1)

				(declare-fun utrc.test1.S1__impl.i1_TO_A (utrc.test1.S1__impl) hermes.iml.aadl.Connection_Real)
				(define-fun utrc.test1.S1__impl.i1_TO_A.init ((x!1 utrc.test1.S1__impl)) Bool
					(and 
						(= (hermes.iml.aadl.Connection_Real.source (utrc.test1.S1__impl.i1_TO_A x!1))  
						   (utrc.test1.S1.i1 (utrc.test1.S1__impl.base_0 x!1))
						)  
						(= (hermes.iml.aadl.Connection_Real.target (utrc.test1.S1__impl.i1_TO_A x!1))  
						   (utrc.test1.S2.i1 (utrc.test1.S1__impl.S2_sub x!1))
						)
					)
				)

				(declare-fun utrc.test1.S1__impl.i2_TO_A (utrc.test1.S1__impl) hermes.iml.aadl.Connection_Real)
				(define-fun utrc.test1.S1__impl.i2_TO_A.init ((x!1 utrc.test1.S1__impl)) Bool
					(and 
						(= (hermes.iml.aadl.Connection_Real.source (utrc.test1.S1__impl.i2_TO_A x!1))  
						   (utrc.test1.S1.i2 (utrc.test1.S1__impl.base_0 x!1))
						)  
						(= (hermes.iml.aadl.Connection_Real.target (utrc.test1.S1__impl.i2_TO_A x!1))  
						   (utrc.test1.S2.i2 (utrc.test1.S1__impl.S2_sub x!1))
						)
					)
				)

				(declare-fun utrc.test1.S1__impl.S2_TO_o1 (utrc.test1.S1__impl) hermes.iml.aadl.Connection_Real)
				(define-fun utrc.test1.S1__impl.S2_TO_o1.init ((x!1 utrc.test1.S1__impl)) Bool
					(and 
						(= (hermes.iml.aadl.Connection_Real.source (utrc.test1.S1__impl.S2_TO_o1 x!1))  
						   (utrc.test1.S2.o1 (utrc.test1.S1__impl.S2_sub x!1))
						)  
						(= (hermes.iml.aadl.Connection_Real.target (utrc.test1.S1__impl.S2_TO_o1 x!1))  
						   (utrc.test1.S1.o1 (utrc.test1.S1__impl.base_0 x!1))
						)
					)
				)

				(declare-fun inst () utrc.test1.S1__impl)
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
						(=>
							(utrc.test1.S2.a1 (utrc.test1.S1__impl.S2_sub inst))
							(utrc.test1.S2.g1 (utrc.test1.S1__impl.S2_sub inst))
						)
						(utrc.test1.S1.a1 (utrc.test1.S1__impl.base_0 inst))
					)
				)
			)
		)
	)

	(edge e2 __ n1.g
		(smt25 ((utrc.test1.S1.g1  (utrc.test1.S1__impl.base_0 inst))))
	)

	(edge e3 __ n2.kb 
		(smt25 
			((declare-sort hermes.iml.aadl.Connection_Real 0)
				(declare-fun hermes.iml.aadl.Connection_Real.source (hermes.iml.aadl.Connection_Real) Real) 
				(declare-fun hermes.iml.aadl.Connection_Real.target (hermes.iml.aadl.Connection_Real) Real) 
				(define-fun hermes.iml.aadl.Connection_Real.a1 ((x!1 hermes.iml.aadl.Connection_Real)) Bool
					(= (hermes.iml.aadl.Connection_Real.source x!1) (hermes.iml.aadl.Connection_Real.target x!1))
				)


				(declare-sort utrc.test1.S1 0)
				(declare-fun utrc.test1.S1.i1 (utrc.test1.S1) Real)
				(declare-fun utrc.test1.S1.i2 (utrc.test1.S1) Real)
				(declare-fun utrc.test1.S1.o1 (utrc.test1.S1) Real)
				(declare-fun utrc.test1.S1.n (utrc.test1.S1) Int)
				(define-fun utrc.test1.S1.a1 ((x!1 utrc.test1.S1)) Bool 
					(and
						(>= (utrc.test1.S1.n x!1) 1)  
						(exists ((x Int)(y Int)) 
							(and
								(and  
									(>= y 1)
									(<= y (utrc.test1.S1.n x!1))
									(>= x 1)
									(<= x (utrc.test1.S1.n x!1))
								)
								(and   
									(or 
										(= (utrc.test1.S1.i1 x!1) (to_real (/ x (utrc.test1.S1.n x!1))))
										(= (utrc.test1.S1.i1 x!1) (* -1 (to_real (/ x (utrc.test1.S1.n x!1)))))
									)
									(or 
										(= (utrc.test1.S1.i2 x!1) (to_real (/ y (utrc.test1.S1.n x!1))))
										(= (utrc.test1.S1.i2 x!1) (* -1 (to_real (/ y (utrc.test1.S1.n x!1)))))
									)
								)
							)
						)
					)
				)

				(define-fun utrc.test1.S1.g1 ((x!1 utrc.test1.S1)) Bool
					(and (<= (utrc.test1.S1.o1 x!1) 1) 
						 (>= (utrc.test1.S1.o1 x!1) 1)
					)
				)

				(declare-sort utrc.test1.S2 0)
				(declare-fun utrc.test1.S2.i1 (utrc.test1.S2) Real)
				(declare-fun utrc.test1.S2.i2 (utrc.test1.S2) Real)
				(declare-fun utrc.test1.S2.o1 (utrc.test1.S2) Real)
				(declare-fun utrc.test1.S2.alpha (utrc.test1.S2) Real)
				(define-fun utrc.test1.S2.a1 ((x!1 utrc.test1.S2)) Bool 
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

				(define-fun utrc.test1.S2.g1 ((x!1 utrc.test1.S2)) Bool
					(= (utrc.test1.S2.o1 x!1) 
						(+
							(* 
								(utrc.test1.S2.i1 x!1)
								(pow (to_real 2) 0.5)
								;(sin (utrc.test1.S2.alpha x!1))
							)
							(*
								(utrc.test1.S2.i2 x!1)
								(pow (to_real 2) 0.5)
								;(cos (utrc.test1.S2.alpha x!1))
							)
						)	
					) 
				)

				(declare-sort utrc.test1.S1__impl 0)
				(declare-fun utrc.test1.S1__impl.S2_sub (utrc.test1.S1__impl) utrc.test1.S2)
				(declare-fun utrc.test1.S1__impl.base_0 (utrc.test1.S1__impl) utrc.test1.S1)

				(declare-fun utrc.test1.S1__impl.i1_TO_A (utrc.test1.S1__impl) hermes.iml.aadl.Connection_Real)
				(define-fun utrc.test1.S1__impl.i1_TO_A.init ((x!1 utrc.test1.S1__impl)) Bool
					(and 
						(= (hermes.iml.aadl.Connection_Real.source (utrc.test1.S1__impl.i1_TO_A x!1))  
						   (utrc.test1.S1.i1 (utrc.test1.S1__impl.base_0 x!1))
						)  
						(= (hermes.iml.aadl.Connection_Real.target (utrc.test1.S1__impl.i1_TO_A x!1))  
						   (utrc.test1.S2.i1 (utrc.test1.S1__impl.S2_sub x!1))
						)
					)
				)

				(declare-fun utrc.test1.S1__impl.i2_TO_A (utrc.test1.S1__impl) hermes.iml.aadl.Connection_Real)
				(define-fun utrc.test1.S1__impl.i2_TO_A.init ((x!1 utrc.test1.S1__impl)) Bool
					(and 
						(= (hermes.iml.aadl.Connection_Real.source (utrc.test1.S1__impl.i2_TO_A x!1))  
						   (utrc.test1.S1.i2 (utrc.test1.S1__impl.base_0 x!1))
						)  
						(= (hermes.iml.aadl.Connection_Real.target (utrc.test1.S1__impl.i2_TO_A x!1))  
						   (utrc.test1.S2.i2 (utrc.test1.S1__impl.S2_sub x!1))
						)
					)
				)

				(declare-fun utrc.test1.S1__impl.S2_TO_o1 (utrc.test1.S1__impl) hermes.iml.aadl.Connection_Real)
				(define-fun utrc.test1.S1__impl.S2_TO_o1.init ((x!1 utrc.test1.S1__impl)) Bool
					(and 
						(= (hermes.iml.aadl.Connection_Real.source (utrc.test1.S1__impl.S2_TO_o1 x!1))  
						   (utrc.test1.S2.o1 (utrc.test1.S1__impl.S2_sub x!1))
						)  
						(= (hermes.iml.aadl.Connection_Real.target (utrc.test1.S1__impl.S2_TO_o1 x!1))  
						   (utrc.test1.S1.o1 (utrc.test1.S1__impl.base_0 x!1))
						)
					)
				)

				(declare-fun inst () utrc.test1.S1__impl)
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
				
				(assert (utrc.test1.S1.a1 (utrc.test1.S1__impl.base_0 inst)))
		))
	)

	(edge e4 __ n2.g
		(smt25 ((utrc.test1.S2.a1 (utrc.test1.S1__impl.S2_sub inst))))
	)

	(edge e5 n1.valid n3.in (boolX (__)))
	(edge e6 n2.valid n3.in (boolX (__)))
	(edge e7 n3.out n4.in (boolX (__)))
	
	(edge e8 n1.cmodel __ (evaluate ((get-value (r1)))))
)
