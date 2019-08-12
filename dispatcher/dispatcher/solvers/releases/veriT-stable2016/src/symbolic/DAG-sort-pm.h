/*
Copyright (c) 2009-2013, INRIA, Universite de Nancy 2 and Universidade
Federal do Rio Grande do Norte.
All rights reserved.

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are met:
   * Redistributions of source code must retain the above copyright
     notice, this list of conditions and the following disclaimer.
   * Redistributions in binary form must reproduce the above copyright
     notice, this list of conditions and the following disclaimer in the
     documentation and/or other materials provided with the distribution.
   * Neither the name of the Universite de Nancy 2 or the Universidade Federal
     do Rio Grande do Norte nor the names of its contributors may be used
     to endorse or promote products derived from this software without
     specific prior written permission.

THIS SOFTWARE IS PROVIDED BY INRIA, Universite de Nancy 2 and
Universidade Federal do Rio Grande do Norte ''AS IS'' AND ANY EXPRESS
OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
DISCLAIMED. IN NO EVENT SHALL INRIA, Université de Nancy 2 and
Universidade Federal do Rio Grande do Norte BE LIABLE FOR ANY DIRECT,
INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
(INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT,
STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING
IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
POSSIBILITY OF SUCH DAMAGE.

*/

#ifndef DAG_SORT_PM_H
#define DAG_SORT_PM_H

#include "assoc.h"

#include "DAG.h"
#include "DAG-sort.h"
#include "list.h"

/**
   \brief Checks if sort1 subsumes sort2
   \param sort1 a sort
   \param sort2 a sort
   \returns 1 if sort1 subsumes sort2, 0 otherwise.
   \remark sort1 subsumes sort2 iff there is a substitution of sort variables
   s such that s(sort1) = sort2 */
extern int       DAG_sort_subsumes(Tsort sort1, Tsort sort2);

/*
  --------------------------------------------------------------
  sort unification
  --------------------------------------------------------------
*/

/*
  Sort unification is used to handle polymorphism.

  Sort unification is done in four steps.

  First all relevant sort unification constraints are collected in a
  list, using function DAG_sort_unif_constrain. Second DAG_sort_unif_solve
  is applied to the list. The result is the most general unifier (mgu) and
  is represented as a list of assocs with key a sort variable and
  value a sort. 

  Third, the mgu defines a sort substitution and may be applied to
  sorts and DAGs (DAG_sort_subst_DAG).

  Finally, when the mgu is no longer useful it shall be destructed
  with DAG_sort_unif_delete.
*/

/**
   \brief adds a sort unification constraint
   \param Plist a pointer to a list of sort constraints
   \param sort1 a sort
   \param sort2 a sort
   \note The list pointed to by Plist is added the constraint formed
   by sort1 and sort2, or left unchanged.
   - A constraint is represented by an association of sort1 with sort2
   (Tassoc). If either one is polymorphic while the other is not, 
   then it is set as the key of the association.
   - If sort1 == sort2, the list pointed to by Plist is left unchanged
   - If the constraint formed by sort1 and sort2 is trivially
   not satisfiable, the program halts and an error message is printed.
   \remark Ref: "Types and Programming Languages", by Benjamin C. Pierce */
extern void DAG_sort_unif_constrain(Tlist * Plist, Tsort sort1, Tsort sort2);

/**
   \brief computes the most general unifier (mgu) for sort unification
   constraints
   \param Plist a pointer to the list of sort unification 
   constraints
   \remark When the function returns Plist points to a list of assoc
   pairs that store the mgu sort substitution.
   \sa DAG_sort_unif_constrain */
extern void DAG_sort_unif_solve(Tlist * Plist);

/**
   \brief destructor for a sort substitution
   \param Plist pointer to the list of sort substitutions */
extern void DAG_sort_unif_delete(Tlist * Plist);

/**
   \return returns the unification of sort1 and sort2, if any.
   \return NULL if there is no unification.
   \sa DAG_sort_unify_n_v2, DAG_sort_unify_n_v1, DAG_sort_unify_n */
extern Tsort DAG_sort_unif_pair(Tsort sort1, Tsort sort2);

/**
   \param PDAG Array of DAGs for function application arguments
   \param Psort Array of sorts of function formal parameters
   \param n Size of PDAG and Psort
   \param sort Sort of function result
   \return returns the result of the unification of sort by the most
   general unifier of sorts of PDAG and Psort, if any.
   \return NULL if there is no most general unifier.
   \sa DAG_sort_subst_sort, DAG_sort_unif_pair */
extern Tsort DAG_sort_unif_apply(const TDAG * PDAG, const Tsort * Psort, 
                                 const unsigned n, const Tsort sort);

/**
   \param PDAG Array of DAGs for function application arguments
   \param sort1 Sort of function formal parameters
   \param n Size of PDAG
   \param sort2 Sort of function result
   \return returns the result of the unification of sort2 by the most
   general unifier of sorts of PDAG and sort1, if any
   \return NULL if there is no most general unifier 
   \sa DAG_sort_unify_apply */
extern Tsort DAG_sort_unif_apply_polyadic(const TDAG * PDAG, const Tsort sort1, 
                                          const unsigned n, const Tsort sort2);

/**
   \brief Applies a sort substitution to a DAG
   \param list a list of sort association pairs
   \param src a DAG
   \return the result of the sort substitution <b>list</b> applied to 
   <b>DAG</b>.
   \pre Every key in <b>list</b> is a sort variable. The DAG
   <b>src</b> may contain binders, but should satisfy the post-condition
   of <tt>binder_rename</tt>.
   \remark Calling this routine has side-effects:
   - on the field  <tt>binding</tt> of existing sorts;
   - on the fields <tt>Pflag</tt> and <tt>flag</tt> of <b>src</b> 
   and its sub-DAGs.
   \remark Complexity: linear in the size of <b>src</b>,
   \remark Does not decrease <tt>src</tt>'s reference counter.
*/
extern TDAG DAG_sort_subst_DAG(Tlist list, TDAG src);

/**
   \brief Creates a copy of (polymorphic) sort
   \param sort a sort, possibly a sort constructor applied to sort variables
   \return the result of the substitution in <b>sort</b> of each sort variable
   with a fresh sort variable
   \pre The binding attribute of <b>sort</b> and its sub-sorts is available 
   (i.e. NULL). This condition is not checked in the function */
extern Tsort DAG_sort_intern(Tsort sort);

#endif /* DAG_SORT_PM_H */
