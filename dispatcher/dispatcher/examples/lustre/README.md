
# README

This package contains 6 Lustre models (S1, S2, S3, T1, T2, and T3) that correspond to 6 scenarios of the same system, a keypad-controlled door lock.

The system consists of a main component, `Lock`, and two subcomponents, `Keypad` and `Control`. Each component has an assume-guarantee contract.

Kind 2 is able to perform compositional analysis over the model using the contracts as abstractions of the components. From the summary of the result, the user can infer which components or contracts should be changed, if any.

The results are output in plain text by default, but they can be dumped in XML or JSON format by passing "-xml" or "-json" when calling Kind 2.


**NOTE 1:** The amount of information currently printed on the standard output by Kind 2's analysis can be overwhelming. However, this is done just to showcase Kind 2's various capabilities (compositional and modular analysis, ability to reason about multiple properties at once, incremental result generation, construction of counter-example traces, and so on).
The **important point** is that all this detailed information is also available in structured format (XML or JSON), hence a specific frontend can choose exactly what to display to the user and how.

**NOTE 2:** In the following, we will talk about a contract for a component and its _implementation_. Since these are models, we are not referring to actual implementations but low-level, executable specifications (from which an actual implementations can be derived, often automatically). In Lustre terms, a component is modeled as a _node_. The assumptions and guarantees associated with the node, together with the node's signature, constitute its contract. The definition of the node, the body, is the "implementation".


## Scenario S1

#### Command:

    kind2 --compositional true --modular true Door_lock_S1.lus

#### Extracted explanation from summary:

`Lock` does not always satisfy the assumption `A1` of `Control` and `A2` of `Keypad`. Additionally, the implementation of `Lock` does not satisfy one of its contract's guarantees (`R1`). However, that might be a consequence of the problem with the assumption above, which prevent Kind 2 from relying on the guarantees of `Control` and and `Keypad` to prove `Lock`'s guarantees.
This suggests that the user should check whether those assumptions are stronger than necessary, or whether the implementation of `Lock` must be fixed to satisfy them. 

## Scenario S2

#### Command:

    kind2 --compositional true --modular true Door_lock_S2.lus

#### Relationship with previous scenario:

`Keypad`'s assumptions have been weakened by commenting out assumption `A2`.

#### Extracted explanation from summary:

Assumption `A2` of `Keypad` is in fact not needed to prove the guarantees in `Keypad`'s contract. However, that contract is not strong enough to prove the guarantees of `Lock`'s contract. Those guarantees *can* be proved using  `Keypad`'s _implementation_ together with `Control`'s contract. This means that `Keypad`'s contract should be strengthened to reflect the stronger guarantees provided by its implementation.

## Scenario S3

#### Command:

    kind2 --compositional true --modular true Door_lock_S3.lus

#### Relationship with previous scenario:

`Keypad`'s contract has been strengthened with guarantee `R4`.

#### Extracted explanation from summary:

The contracts of subcomponents `Control` and `Keypad` are strong enough to prove the guarantees of `Lock`'s contract without considering their implementation. Moreover, the implementation of each of the three components satisfies its respective contract.
Everything checks out fine. This is the best case scenario for a multi-component system.

## Scenario T1

#### Command:

    kind2 --compositional true --modular true Door_lock_T1.lus

* Relationship with previous scenario:

`Keypad`'s contract has been strengthened with guarantee `R0`. For argument's sake, pretend here that we do not know about the previous scenarios.

#### Extracted explanation from summary:

Guarantee `R0` is not satisfied. Locally, this would suggest that `Keypad`'s assumptions should be strengthened, or `Keypad`'s implementation should be fixed to satisfy `R0`.
However, Kind 2 is still able to prove the system-level guarantees (those of `Lock`'s contract) using the other guarantees of `Keypad`. This shows that `R0` is in fact superfluous for this system and so it could simply be dropped.

**Note:** If `R0` _was_ satisfied by `Keypad`'s implementation it would still be superfluous in the context of this system. However, Kind 2's analysis would not able to detect that. In a similar way, when everything checks out, the analysis will not be able to detect superfluous assumptions either. For those cases, one needs to explicitly implement in Kind 2 the capability to do what we call "merit assignment" (the dual of the blame assignment capability developed in the VERDICT project and used in case of falsified guarantees). We plan to add merit assignment capabilities to Kind 2 later in the project.


## Scenario T2

#### Command:

    kind2 --compositional true --modular true Door_lock_T2.lus

#### Relationship with previous scenario:

`Keypad`'s assumptions have been strengthened with assumption `A2`.
Again, pretend we do not know about the previous scenarios. Also, suppose we have strong reasons to have `A2`.

#### Extracted explanation from summary:

As in Scenario S1, either the assumptions `A1` of `Control` and `A2` of `Keypad` are stronger than necessary, or the implementation of `Lock` must be fixed to satisfy those assumptions.
From the architecture of the system we can reasonably conjecture that the problem with `Control` is probably a spurious one, just a consequence of the analysis being unable to rely in `Lock` on the guarantees of `Keypad` since one of `Keypad`'s assumptions is falsified. Hence we can focus on assumption `A2` of `Keypad` first.

## Scenario T3

#### Command:

    kind2 --compositional true --modular true Door_lock_T3.lus

#### Relationship with previous scenario:

`Lock`'s implementation has been changed to satisfy `Keypad`'s assumptions, by bringing down to 9 any value of `Digit` that is greater than that.
Since `Digit` is an input for `Lock` too, an alternative could have been to strengthen `Lock`'s contract with the assumption that `Digit` does not exceed 9.

#### Extracted explanation from summary:

Everything fully checks. We are done. The contracts of `Control` and `Keypad` are strong enough to prove the guarantees of `Lock`'s contract without considering their implementation. Moreover, the respective implementations of both `Control` and `Keypad` satisfy the corresponding contract.
