(set-logic QF_NRA)
(declare-sort hermes.iml.aadl.Connection_Real 0)
(declare-sort utrc.test1.S1__impl 0)
(declare-fun hermes.iml.aadl.Connection_Real.source (hermes.iml.aadl.Connection_Real) Real)
(declare-fun utrc.test1.S1__impl.i1_TO_A (utrc.test1.S1__impl) hermes.iml.aadl.Connection_Real)
(declare-fun inst () utrc.test1.S1__impl)
(assert 
    (= 
;       0.5
;        0.5
      (hermes.iml.aadl.Connection_Real.source (utrc.test1.S1__impl.i1_TO_A inst)) 
      (hermes.iml.aadl.Connection_Real.source (utrc.test1.S1__impl.i1_TO_A inst)) 
    )
) 
(check-sat)

