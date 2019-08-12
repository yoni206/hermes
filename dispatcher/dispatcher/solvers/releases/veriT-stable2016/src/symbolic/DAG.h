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

/**
   \file DAG.h
   \author Pascal Fontaine

   \brief Module for terms and formulas
   - Formulas and terms are represented by DAGs
   - Maximal sharing is used (two identical DAGs are merged)

   \todo Some things could be better:
   - polymorphism, subsorts
   - sorts should be unifiable
   - one should be able to use several "integer sort", let's say
   apple numbers and banana numbers
   - Attribute lists or Hash tables or both...
   - Hash table for symbols
   - optional on-the-fly type checking.
   - Functional simplification (that only depend on argument),
   and bit for functional simplification: apply simp on building terms */

/* TODO
   remove misc
   Clean hash */

#ifndef __DAG_H
#define __DAG_H

#include <stdarg.h>

#include "stack.h"

#include "DAG-sort.h"
#include "DAG-symb.h"

/*
  --------------------------------------------------------------
  Main datastructure
  --------------------------------------------------------------
*/

typedef uint32_t TDAG; /** TDAG: 2**32-1 possible values */

TSstack(_DAG, TDAG); /* typedefs Tstack_DAG */
TSstack(_DAGstack, Tstack_DAG); /* typedefs Tstack_DAGstack */

/** \brief special (NULL) value for type TDAG */
#define DAG_NULL ((TDAG) 0)

/**
 \brief Structure to represent DAGs, i.e. perfectly shared terms.

 The structure contains the head symbol, the arity, references to
 the sub-terms, and some flags.

 The structure is designed to hold in 16 bytes:
 - 4 bytes for the head symbol
 - 4 bytes for the arity and the flags
 - 8 bytes for the sub-terms

 The arity defines the access to sub-terms.
 - arity = 1, 2: args.bin.arg0, args.bin.arg1
 - arity >= 2: args.PDAG is a pointer to an array of TDAG

 There are 8 bytes unused for terms of arity 0, and 4 bytes unused for terms of
 arity 1.

 The flags are:
 - quant: the term contains a quantified sub-term (possibly itself)
 - ground: the term does not contain free variables. */
struct TSDAG
{
  /** \brief topmost symbol */
  Tsymb     symb;
#ifndef PEDANTIC
  /** \brief size of the array of sub-terms */
  unsigned  arity : 30;
  /** \brief indicates if DAG contains quantifiers (set on DAG construction) */
  bool      quant : 1;
  /** \brief indicates if DAG is ground (call qnt_ground on a DAG to set the ground bit on all (sub)terms) */
  bool      ground : 1;
#else
  unsigned  arity;
  bool      quant;
  bool      ground;
#endif
  /** \brief sub-terms */
  union {
    TDAG     *PDAG; /* array of sub-terms iff arity > 2 */
    struct {
      TDAG DAG0;    /* first sub-term iff arity <= 2 */
      TDAG DAG1;    /* second sub-term iff arity == 2 */
    } bin;
  } args;
};

TSstack(_SDAG, struct TSDAG);

/** \brief The DAG table stored in a single chunk of memory */
extern Tstack_SDAG DAG_table;

#define __DAG_DATA(DAG) (DAG_table->data[(TDAG) (DAG)])

extern struct DAG_attr {
  /** \brief sort */
  Tsort     *sort;
  /** \brief field for user */
  int32_t   *misc;
  /** \brief (private) hash key or next in free list*/
  uint32_t  *hash_key;
} DAG_attr;

/*
  --------------------------------------------------------------
  Accessors
  --------------------------------------------------------------
*/

/** \brief DAG symbol */
#define DAG_symb(DAG) (__DAG_DATA(DAG).symb)
/** \brief DAG sort */
#define DAG_sort(DAG) (DAG_attr.sort[DAG])
/**  \brief DAG arity */
#define DAG_arity(DAG) (__DAG_DATA(DAG).arity)

/** \brief Array of DAG args */
#define DAG_args(DAG) ((DAG_arity(DAG) > 2)?__DAG_DATA(DAG).args.PDAG:  \
                       &(__DAG_DATA(DAG).args.bin.DAG0))

#ifdef DEBUG
/** \brief DAG's first arg (only for unary/binary applications) */
static inline TDAG
DAG_arg0(const TDAG DAG)
{
  assert(DAG_arity(DAG) <= 2);
  return (__DAG_DATA(DAG).args.bin.DAG0);
}
/** \brief DAG's second arg (only for binary applications) */
static inline TDAG
DAG_arg1(const TDAG DAG)
{
  assert(DAG_arity(DAG) <= 2);
  return (__DAG_DATA(DAG).args.bin.DAG1);
}
/** \brief DAG's (i-1)-th arg, general case*/
static inline TDAG
DAG_arg(const TDAG DAG, const unsigned i)
{
  assert(i < DAG_arity(DAG));
  return DAG_args(DAG)[i];
}
/** \brief DAG's last arg, general case */
static inline
TDAG DAG_arg_last(const TDAG DAG)
{
  assert(DAG_arity(DAG));
  return DAG_args(DAG)[DAG_arity(DAG) - 1];
}
#else
#define DAG_arg0(DAG) (__DAG_DATA(DAG).args.bin.DAG0)
#define DAG_arg1(DAG) (__DAG_DATA(DAG).args.bin.DAG1)
#define DAG_arg(DAG, i) (DAG_args(DAG)[i])
#define DAG_arg_last(DAG) (DAG_args(DAG)[DAG_arity(DAG) - 1])
#endif

/** \brief DAG misc */
#define DAG_misc(DAG) (DAG_attr.misc[DAG])
/** \brief DAG misc */
#define DAG_misc_set(DAG, val) (DAG_attr.misc[DAG] = (val))
/** \brief DAG contains quantifiers */
#define DAG_quant(DAG) (__DAG_DATA(DAG).quant)

extern bool DAG_quant_f(TDAG DAG);

/** \brief DAG is ground */
#define DAG_ground(DAG) (__DAG_DATA(DAG).ground)
/** \brief DAG hash key */
#define DAG_key(DAG) (DAG_attr.hash_key[DAG])

/*
  --------------------------------------------------------------
  Constructors - Destructors
  --------------------------------------------------------------
*/

/**
   \brief DAG constructor
   \param symb topmost symbol
   \param arity number of sub-terms
   \param PDAG array of subterms
   \return Creates (if new) and returns TDAG from symb and PDAG.
   \remark Destructive for PDAG */
extern TDAG      DAG_new(Tsymb symb, unsigned arity, TDAG * PDAG);

/**
   \brief DAG constructor for null-ary functios (constants)
   \param symb topmost symbol
   \return Creates (if new) and returns TDAG from symb. */
extern TDAG      DAG_new_nullary(Tsymb symb);

/**
   \brief DAG constructor for unary functions
   \param symb topmost symbol
   \param arg subterm
   \return Creates (if new) and returns TDAG from symb and arg. */
extern TDAG      DAG_new_unary(Tsymb symb, TDAG arg);

/**
   \brief DAG constructor for binary functions
   \param symb topmost symbol
   \param arg0 first argument
   \param arg1 second argument
   \return Creates (if new) and returns TDAG from symb and PDAG.
   \remark Destructive for PDAG */
extern TDAG      DAG_new_binary(Tsymb symb, TDAG arg0, TDAG arg1);

/**
   \brief DAG constructor
   \param symb The topmost symbol of the constructed term.
   \param ... subterms, followed by NULL.
   \pre The number of subterms needs to be compatible with the arity of symb
   \return Creates (if new) and returns TDAG from symb and given arguments */
extern TDAG      DAG_new_args(Tsymb symb, ...);

/**
   \brief like DAG_new, but with a stack for sub terms
   \param symb the top-most symbol
   \param stack_arg the stack of arguments
   \remark non destructive for the stack */
extern TDAG      DAG_new_stack(Tsymb symb, Tstack_DAG stack_arg);

/**
   \brief Reference counter increment
   \param DAG its reference counter will be incremented
   \return the result is the same as the argument */
extern TDAG      DAG_dup(TDAG DAG);

/**
   \brief Destructor.
   \param DAG to be freed
   \remark The reference counter of DAG is decremented. If the resulting value
   is zero, then DAG is freed */
extern void      DAG_free(TDAG DAG);

/*
  --------------------------------------------------------------
  Fundamental data structure and handling functions
  --------------------------------------------------------------
*/

/**
    \brief tests if DAG f is a literal
    \param f a DAG
    \pre f is of sort SORT_BOOLEAN */
#define DAG_literal(f) ((f) && ( !boolean_connector(DAG_symb(f)) ||	\
                                 (DAG_symb(f) == CONNECTOR_NOT &&	\
                                  !boolean_connector(DAG_symb(DAG_arg0(f))))))

/** \brief TDAG version of generic functions, to instantiate data containers */
extern unsigned DAG_hash(TDAG DAG);
extern int      DAG_equal(TDAG DAG1, TDAG DAG2);
extern int      DAG_cmp(TDAG DAG1, TDAG DAG2);
extern int      DAG_cmp_q(TDAG *PDAG1, TDAG *PDAG2);

/**
    \brief Whether a DAG is an a Tstack_DAG
    \remark Assumes stack is sorted. */
extern bool stack_DAG_contains(Tstack_DAG stack, TDAG DAG);

/**
    \author Haniel Barbosa
    \brief computes intersection of two given DAG stacks
    \param stack0 first stack
    \param stack1 second stack
    \remark assumes stacks are sorted
    \remark [TODO] O(n log m) solution by ordering smaller stack, then
    performing binary search on it for each element of the bigger stack. */
extern Tstack_DAG stack_DAG_intersect(Tstack_DAG stack0, Tstack_DAG stack1);

/**
    \author Haniel Barbosa
    \brief whether two stacks are the same
    \param stack0 first stack
    \param stack1 second stack
    \remark assumes stacks are sorted */
extern bool stack_DAG_equal(Tstack_DAG stack0, Tstack_DAG stack1);

/**
    \author Haniel Barbosa
    \brief whether the first given stack is contained in the second
    \param stack0 first stack
    \param stack1 second stack
    \remark assumes stacks are sorted */
extern bool stack_DAG_subset(Tstack_DAG stack0, Tstack_DAG stack1);

/**
    \author Haniel Barbosa
    \brief computes difference of two given DAG stacks
    \param stack0 first stack
    \param stack1 second stack
    \remark assumes stacks are sorted */
extern Tstack_DAG
stack_DAG_difference(Tstack_DAG stack0, Tstack_DAG stack1);

/*
  --------------------------------------------------------------
  Initialisation-release functions
  --------------------------------------------------------------
*/

/**
   \brief Initializes veriT-DAG module.
   \remark Module options must have been initialized before veriT-DAG module */
extern void      DAG_init(void);

/**
   \brief Closes veriT-DAG module, frees all allocated data structures.
   \remark Module options must be closed after veriT-DAG module */
extern void      DAG_done(void);

typedef void (*TDAG_hook_resize) (unsigned old, unsigned new);
typedef void (*TDAG_hook_free) (TDAG);

/**
   \brief adds a function to be notified of the resizing of the DAG stack
   \param hook_resize the function to call at each resize
   \remark new size is given as argument of hook_resize
   \remark if used to allocate side information, hook_resize should be used
   to allocate and initialize this information */
extern void DAG_set_hook_resize(TDAG_hook_resize hook_resize);

/**
   \brief adds a function to be notified of the freeing of a DAG
   \param hook_free the function to call at each DAG free
   \remark DAG which is free given as argument of hook_free
   \remark use as reinitialization of side information linked with DAG */
extern void DAG_set_hook_free(TDAG_hook_free hook_free);

#ifdef DEBUG
extern void DAG_table_print(void);
#endif

#endif /* __DAG_H */
