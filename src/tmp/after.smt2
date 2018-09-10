(set-logic QF_NRA)
(declare-fun inst.base_0.i1 () Real)
(declare-fun inst.base_0.i2 () Real)
(declare-fun inst.base_0.o1 () Real)
(declare-fun inst.base_0.n () Int)

(declare-fun inst.S2_sub.i1 () Real)
(declare-fun inst.S2_sub.i2 () Real)
(declare-fun inst.S2_sub.o1 () Real)
(declare-fun inst.S2_sub.alpha () Real)

(declare-fun x () Int)
(declare-fun y () Int)

(assert 
	(and 
		(=>
			(and   
				(or 
					(= inst.S2_sub.i1 1)
					(= inst.S2_sub.i1 -1)
				)
				(or 
					(= inst.S2_sub.i2 0)
					(= inst.S2_sub.i2 1)
					(= inst.S2_sub.i2 -1)
				)
			)
			(= inst.S2_sub.o1 
				(+
					(* 
						inst.S2_sub.i1
						;;(^ 2 0.5)
						(sin inst.S2_sub.alpha)
					)
					(*
						inst.S2_sub.i2
						;;(^ 2 0.5)
						(cos inst.S2_sub.alpha)
					)
				)	
			) 
		)
		(and
			(= inst.base_0.n 1)  
			
			(or 
			   (= x 1)
			   (= x 2)	
			)
			(or 
			   (= y 1)
			   (= y 2)	
			)
			 
				(and
					(and  
						(>= y 1)
						(<= y inst.base_0.n)
						(>= x 1)
						(<= x inst.base_0.n)
					)
					(and   
						(or 
							(= inst.base_0.i1 (/ x inst.base_0.n))
							(= inst.base_0.i1 (* -1 (/ x inst.base_0.n)))
						)
						(or 
							(= inst.base_0.i2 (/ y inst.base_0.n))
							(= inst.base_0.i2 (* -1 (/ y inst.base_0.n)))
						)
					)
				)
			
		)
		(= inst.base_0.i1 inst.S2_sub.i1)
		(= inst.base_0.i2 inst.S2_sub.i2)
		(= inst.base_0.o1 inst.S2_sub.o1)
		(not 
			(and (<= inst.base_0.o1 2.001) 
			     (>= inst.base_0.o1 -2.001)
			)
		)
	)
	
)
(check-sat)
(exit)




