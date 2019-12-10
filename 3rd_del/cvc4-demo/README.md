
# README

This package contains smt2 script files that demonstrate the abduction features of the Satisfiability Modulo Theories (SMT) solver CVC4.
It also contains a compatible binary of CVC4.

The goal of abduction is to provide suggestions to the user for how to fix failed proof goals.
We have extended the input language of CVC4 to support a `get-abduct` command which asks CVC4 to synthesize a predicate that is consistent with a knowledge base and suffices to prove a given goal.

## Example 1: A Simple Example of Abduction

This is a small example to demonstrate the interface of the abduction feature in CVC4.

#### Command:

    cvc4 ex1-simple.smt2

#### Detailed Description:

The file `ex1.smt2` is in the SMT version 2.6 standard format.
A reference of this format can be found here: http://smtlib.cs.uiowa.edu/papers/smt-lib-reference-v2.6-r2017-07-18.pdf.
In this file, first a background logic and options are initialized:
```
(set-logic QF_LIA)
(set-option :produce-abducts true)
```
The logic `QF_LIA` indicates that the formulas in this file are limited quantifier-free (QF) linear integer arithmetic (LIA).
The next line indicates that we are interested in generating abduction predicates in this file.
Then, a set of variables are declared:
```
(declare-fun n () Int)
(declare-fun m () Int)
(declare-fun i () Int)
(declare-fun j () Int)

```
Then, a set of assertions over these variables is given:
```
(assert (and (>= n 0) (>= m 0)))
(assert (< n i))
(assert (< (+ i j) m))
```
We will refer to this set of formulas as our ``knowledge base''.
This can be seen as our knowledge base of facts that are known to be true.
Next, we issue this command:
```
(get-abduct A 
  (<= n m)
)
```
We call the formula `(<= n m)` above our ``goal''.
This can be seen as specifying a fact that the user expects to be implied by the knowledge base.

Here, the user expects that the knowledge base implies that `m` should always be greater than `n`.

The `get-abduct` command asks the SMT solver to find the definition of a predicate `A` that is consistent with our knowledge base that implies our goal.
In more detail, as mentioned our goal is to show that `m` is always larger than `n`.
By our second axiom, we have that `n` is strictly less than `i`, and by our third axiom `m` is strictly greater than `i+j`.
However, this does not suffice to show the goal, since it may be the case that `j` is negative.


#### Expected Output:

```
(define-fun A () Bool (= j i))
```

There are many possible predicates that meet the criteria of being consistent with our set of axioms and implying our goal.
CVC4 will return the first such predicate.
In this case it returns that if `i` were equal to `j`, then the goal is provable.
This indeed suffices to prove the goal (since `i` must be positive as well), although it may not be the best possible explanation.

## Example 2: User-Provided Restrictions

This example demonstrates the user-provided restrictions on the shape of solutions to an abduction problem.

#### Command:

    cvc4 ex2-grammar.smt2

#### Detailed Description:

The axioms and conjecture for this example are the same as in `ex1.smt2`.
However, an additional argument has been provided to the `get-abduct` command:
```
  ((GA Bool) (GI Int))
  (
  (GA Bool ((>= GI GI)))
  (GI Int ((+ GI GI) (- GI) i j 0 1))
  )
```
This specifies a context-free grammar that specifies the class of possible solutions for our abduction predicate `A`.
The start symbol of the grammar is `GA` and its non-terminal symbols are `GA` and `GI`.
In other words, this grammar specifies the class of arithmetic inequalities whose free variables are limited to `i` and `j`.
A full description of the format for specifying grammars of this form can be found in https://sygus.org/assets/pdf/SyGuS-IF_2.0.pdf.
In particular, the second argument to the `get-abduct` command conforms to the <GrammarDef> syntax, in Section 2.8 of this document.

In practice, this feature is useful if the user has some intuition of the content of the missing predicate that their knowledge base lacks.
In the example above, the user may have realized that not enough information regarding `i` and `j` had been given as part of the axioms.

#### Expected Output:

```
(define-fun A () Bool (>= j i))
```
Here, CVC4 has produced a predicate that is a solution to the abduction and meets the syntax restrictions of the user-provided grammar.
It is weaker than the previous solution (which insisted that `j` be equal to `i`), meaning that it is a more useful solution for the user.

## Example 3: Producing Multiple Solutions for Abduction

This example show the ability of CVC4 to produce multiple solutions to an abduction problem.
CVC4 uses an algorithm that streams multiple non-redundant solutions over time.

#### Command:

    cvc4 ex3-multiple.smt2 --sygus-stream
    
#### Detailed Description:

The option `--sygus-stream` tells CVC4 to list multiple solutions to the abduction problem.

#### Expected Output:

```
(define-fun A ((j Int) (i Int) (m Int) (n Int)) Bool (>= j i))
(define-fun A ((j Int) (i Int) (m Int) (n Int)) Bool (>= j n))
(define-fun A ((j Int) (i Int) (m Int) (n Int)) Bool (>= j 0))
(define-fun A ((j Int) (i Int) (m Int) (n Int)) Bool (>= m i))
(define-fun A ((j Int) (i Int) (m Int) (n Int)) Bool (>= m n))
(define-fun A ((j Int) (i Int) (m Int) (n Int)) Bool (>= 0 n))
(define-fun A ((j Int) (i Int) (m Int) (n Int)) Bool (>= 1 i))
...
```
Each of the above predicates is a solution to the abduction problem.
Included in this list is the original intended solution, indicating that `j` is positive.

These predicates are pruned such that CVC4 will not list solutions that equivalent to previously listed ones.
It will also not list solutions that are logically stronger than previous ones, since a logically weaker solution conveys more information to the user.
For example, CVC4 does not include the solution `(>= j 1)` in this list, since the solution `(>= j 0)` is weaker and hence is a better solution.

## Example 4: Scalability and More Theories

This example show the ability of CVC4 to solve abduction problems for larger examples and over other theories such as strings.

#### Command:

    cvc4 ex4-kaluza.smt2

#### Detailed Description:

This smt2 file comes from a web security application.
In contrast to the above example which involves only linear integer arithmetic,
this example also involves strings and regular expressions.

#### Expected Output:

```
(define-fun A () Bool T_SELECT_5)
```

CVC4 is able to find a concise abduct for this problem, in particular, `T_SELECT_5`. 
This may help the user to discover a small fix to a large knowledge base containing a diverse set of constraints.


## Example 5: Non-linear integer arithmetic

This example show the ability of CVC4 to solve abduction problems for challenging logics, namely non-linear integer arithmetic

#### Command:

    cvc4 ex5-termination.smt2 --sygus-stream

#### Detailed Description:

This smt2 file comes from an application involving termination proving.
The benchmark involves non-linear integer arithmetic and asks the SMT solver to find an abduct for a failed goal.

#### Expected Output:

```
(define-fun A () Bool (= lam0n0 lam0n1))
(define-fun A () Bool (= lam0n0 lam1n1))
(define-fun A () Bool (= lam0n0 global_V0_1))
(define-fun A () Bool (= lam0n0 global_invc1_1))
(define-fun A () Bool (= lam0n2 lam0n1))
(define-fun A () Bool (= lam0n2 lam1n1))
(define-fun A () Bool (= lam0n2 global_invc1_0))
(define-fun A () Bool (= lam0n2 global_V0_1))
(define-fun A () Bool (= lam0n2 global_invc1_1))
(define-fun A () Bool (= lam0n1 lam1n0))
(define-fun A () Bool (= lam0n1 lam1n4))
...
...
```

Like the previous example, CVC4 is able to synthesize a number of concise formulas that suffice to show the goal.
These formulas are relatively simple, involving simple arithmetic relationships between the arithmetic inputs.
