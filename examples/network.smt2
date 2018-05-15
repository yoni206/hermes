(! declare-sort iml.lang.DomainSpecificTool 0 :meta-type)


;; Definitions from package network (assumes definitions from iml.lang previously defined)

;The meta information network tool
(! declare-sort network.NetworkTool 0 :meta-type)

; Definition of the Priviledge finite type
(! declare-datatypes 
     ((network.Priviledge 0)) 
     (( (user) (su) (root) )) :type)

; Definition  of Service  as simple uninterpreted Sort
(! declare-sort  network.Service 0 :type)

; Definition  of Host
(! declare-sort network.Host 0 :type :fields (services) )
; fields are defined as functions
(! declare-fun network.Host.services (network.Host) (Set network.Service) :field)

; Definition  of Router as simple uninterpreted Sort
(! declare-sort  network.Router 0 :type)

; Definition  of Network 
(! declare-sort  network.Network 0 :type :fields (hosts routers connect) )
(! declare-fun network.Network.hosts (network.Network) (Set network.Host) :field)
(! declare-fun network.Network.routers (network.Network) (Set network.Router) :field)
(! declare-fun network.Network.connect (network.Network) (Set (Tuple network.Host network.Router)) :field)

;  Definition  of connectRelation   tool interface
(! declare-fun network.connectRelation.p0 () iml.lang.DomainSpecificTool :property)
(! declare-fun network.connectRelation.p () network.NetworkTool :property)
(! declare-fun network.connectRelation (network.Network) (Set (Tuple network.Host network.Host)) :properties (p0 p) )



;; Definitions from package example1 (assumes definitions from network and iml.lang previously defined)

; ssh servive
(! declare-const example1.ssh network.Service :constant)

; Network1
(! declare-sort example1.Network1 0 :type :fields (host1 host2) )
(! declare-fun example1.Network1.host1 (network.Network) network.Host :field :initialized)
; Rember to assert this for each new instance of Network 1
(! define-fun example1.Network1.host1.__init ( (n network.Network) ) Bool
    (member example1.ssh (network.Host.services (example1.Network1.host1 n)) ) :assertion :init)

(! declare-fun example1.Network1.host2 (network.Network) network.Host :field)
(! declare-fun example1.Network1.router (network.Network) network.Router :field)

; Each field in a type is a new variable
; Rember to assert this for each new instance of Network 1
(! define-fun example1.Network1.__new ( (n network.Network)) Bool
    (not (= (example1.Network1.host1 n) (example1.Network1.host2 n) )) :assertion :new)

(! declare-fun example1.Network1.config.a () iml.lang.Assertion :property)
(! define-fun example1.Network1.config ( (n network.Network)) Bool 
  (and (members (mkTuple (example1.Network1.host1 n) (example1.Network1.router n) ) (network.Network.connect n))  
       (members (mkTuple (example1.Network1.host2 n) (example1.Network1.router n) ) (network.Network.connect n)) 
    )
  :assertion :properties (a))




