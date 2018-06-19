(declare-sort iml.lang.DomainSpecificTool 0 :meta-type)

;; Definitions from package network (assumes definitions from iml.lang previously defined)

;The meta information network tool
(declare-sort network.NetworkTool 0 :meta-type)

; Definition  of Service  as simple uninterpreted Sort
(declare-sort  network.Service 0 :type)

; Definition  of Host
(declare-sort network.Host 0 :type :fields (services) )
; fields are defined as functions
(declare-fun network.Host.services (network.Host) network.Service :field)

; Definition  of Router as simple uninterpreted Sort
(declare-sort  network.Router 0 :type)

; Definition  of Network 
(declare-sort  network.Network 0 :type :fields (hosts routers connect) )
(declare-fun network.Network.hosts (network.Network) network.Host :field)
(declare-fun network.Network.routers (network.Network) network.Router :field)
(declare-fun network.Network.connect (network.Network) network.Host :field)

;  Definition  of connectRelation   tool interface
(declare-fun network.connectRelation.p0 () iml.lang.DomainSpecificTool :property)
(declare-fun network.connectRelation.p () network.NetworkTool :property)
(declare-fun network.connectRelation (network.Network)  network.Host :properties (p0 p) )



;; Definitions from package example1 (assumes definitions from network and iml.lang previously defined)

; ssh servive
(declare-const example1.ssh network.Service :constant)

; Network1
(declare-sort example1.Network1 0 :type :fields (host1 host2) )
(declare-fun example1.Network1.host1 (network.Network) network.Host :field :initialized)
; Rember to assert this for each new instance of Network 1
(define-fun example1.Network1.host1.__init ( (n network.Network) ) Bool
    (= example1.ssh (network.Host.services (example1.Network1.host1 n)) ) :assertion :init)

(declare-const n network.Network)

(declare-fun example1.Network1.host2 (network.Network) network.Host :field)
(declare-fun example1.Network1.router (network.Network) network.Router :field)

; Each field in a type is a new variable
; Rember to assert this for each new instance of Network 1
(define-fun example1.Network1.__new ( (n network.Network)) Bool
    (not (= (example1.Network1.host1 n) (example1.Network1.host2 n) )) :assertion :new)

(declare-sort iml.lang.Assertion 0)

(declare-fun example1.Network1.config.a () iml.lang.Assertion :property)

(assert (not (not (= example1.Network1.config.a example1.Network1.config.a))))
(assert (= (example1.Network1.router n)  (example1.Network1.router n)  ))
(check-sat)



