(declare-sort iml.lang.DomainSpecificTool 0 )
;;;;

;; Definitions from package network (assumes definitions from iml.lang previously defined)

;The meta information network tool
(declare-sort network.NetworkTool 0 )


; Definition  of Service  as simple uninterpreted Sort
(declare-sort  network.Service 0 )

; Definition  of Host
(declare-sort network.Host 0 )
; fields are defined as functions
(declare-fun network.Host.services (network.Host) (Set network.Service) )

; Definition  of Router as simple uninterpreted Sort
(declare-sort  network.Router 0 )

; Definition  of Network 
(declare-sort  network.Network 0 )
(declare-fun network.Network.hosts (network.Network) (Set network.Host) )
(declare-fun network.Network.routers (network.Network) (Set network.Router) )
(declare-fun network.Network.connect (network.Network) (Set (Tuple network.Host network.Router)) )

;  Definition  of connectRelation   tool interface
(declare-fun network.connectRelation.p0 () iml.lang.DomainSpecificTool )
(declare-fun network.connectRelation.p () network.NetworkTool )
(declare-fun network.connectRelation (network.Network) (Set (Tuple network.Host network.Host)) )



;; Definitions from package example1 (assumes definitions from network and iml.lang previously defined)

; ssh servive
(declare-const example1.ssh network.Service )

; Network1
(declare-sort example1.Network1 0 )
(declare-fun example1.Network1.host1 (network.Network) network.Host )
; Rember to assert this for each new instance of Network 1
(define-fun example1.Network1.host1.__init ( (n network.Network) ) Bool
     (! (= 0 0) :bla))

(declare-fun example1.Network1.host2 (network.Network) network.Host )
(declare-fun example1.Network1.router (network.Network) network.Router )

; Each field in a type is a new variable
; Rember to assert this for each new instance of Network 1
(define-fun example1.Network1.__new ( (n network.Network)) Bool
    (! (not (= (example1.Network1.host1 n) (example1.Network1.host2 n) )): bli))

(declare-fun example1.Network1.config.a () Bool)
(define-fun example1.Network1.config ( (n network.Network)) Bool 
  (and (= 0 0) (= 0 0)))



