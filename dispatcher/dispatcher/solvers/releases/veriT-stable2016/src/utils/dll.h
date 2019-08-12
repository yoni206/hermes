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
   \file dll.h
   \brief The module provides generic circular doubly-linked list (dll)
   \author David Deharbe
   \author Pascal Fontaine */

#ifndef __DLL_H
#define __DLL_H

#include "types.h"

#define GEN_TYPE uintptr_t
#define GEN_NULL 0

/* PF empty list is NULL pointer.
   internal structure is circular.
   To visit every element in a list, just take cdr 
   until getting original pointer */

typedef unsigned Tdll;
typedef struct TSdll
{
  Tdll next, prev;
  GEN_TYPE data;
} TSdll;  /**< The type for circular lists */

extern TSdll * dll_array;

#define DLL_NULL 0

/**
   \brief Constructor for dll with arguments in it.
   \param data a data of GEN_TYPE, followed by any number of GEN_TYPE datas
   \remarks Last argument should be 0 (of GEN_TYPE)
   \return A dll containing the datas given as arguments, in the same order
   \author Pascal Fontaine */
Tdll      dll_new_args(GEN_TYPE data, ...);

/**
   \brief dll destructor
   \param Pdll address of the destructed list
   \post  Pdll is DLL_NULL
   \author Pascal Fontaine */
void      dll_free(Tdll * Pdll);

/**
   \brief Accessor to first element
   \param dll a dll
   \pre dll is not DLL_NULL
   \return the first element of dll
   \author Pascal Fontaine */
#define dll_car(dll) (dll_array[dll].data)

/**
   \brief Accessor to last element
   \param dll a dll
   \pre dll is not DLL_NULL
   \return the last element of dll
   \author Pascal Fontaine */
#define dll_last(dll) (dll_array[dll_array[dll].prev].data)

/**
   \brief Returns dll rotated one element left (tail to head)
   \param dll a dll
   \pre dll is not DLL_NULL
   \return  a dll such that i-th elmt is i+1-th elmt of argument and
   the last element is the first element of dll
   \remarks The result can be viewed as the tail of dll
   \warning The result and dll share the same nodes
   \warning The resulting dll has the same length as the argument dll
   \remarks Constant time
   \author Pascal Fontaine */
#define dll_cdr(dll) (dll_array[dll].next)

/**
   \brief Returns dll rotated one element right (head to tail)
   \param dll a dll
   \pre dll is not DLL_NULL
   \return  a dll such that i-th elmt is i-1-th elmt of argument and
   the first element is the last element of dll
   \warning The result and dll share the same nodes
   \warning The resulting dll has the same length as the argument dll
   \remarks Constant time
   \author Pascal Fontaine */
#define dll_prev(dll) (dll_array[dll].prev)

/**
   \brief Length of dll
   \param dll a dll
   \return the number of elements in dll
   \remarks Linear time.
   \author Pascal Fontaine */
unsigned  dll_length(Tdll dll);

/**
   \brief dll copy
   \param dll a dll
   \return a copy of dll, the order is preserved
   \remark Linear time
   \author Pascal Fontaine */
Tdll      dll_cpy(Tdll dll);

/**
   \brief Creates a dll with a single element
   \param data a data
   \return dll containing single element data
   \remarks Constant time */
Tdll      dll_one(GEN_TYPE data);

/**
   \brief Adds element to head of dll
   \param data a data
   \param dll a dll
   \return dll with head containing data and tail equal to dll.
   \remarks Constant time
   \remarks destructive for dll */
Tdll      dll_cons(GEN_TYPE data, Tdll dll);

/**
   \brief Adds element to tail of dll
   \param data a data
   \param dll a dll
   \return dll with elements of argument followed by data
   \remarks Constant time
   \remarks destructive for dll */
Tdll      dll_add(Tdll dll, GEN_TYPE data);

/**
   \brief Replace by P first element of dll.
   \param dll a dll
   \param data a data
   \return dll with elements of argument dll, but data instead of first element
   \remarks The argument is modified in place and returned
   \remarks Constant time
   \remarks destructive for dll */
Tdll      dll_set_car(Tdll dll, GEN_TYPE data);

/**
   \brief accessor based on position
   \param dll a dll
   \param n a position
   \return element at position n of dll if it exists, 0 otherwise
   \remark O(n) */
GEN_TYPE  dll_n(Tdll dll, unsigned n);

/**
   \brief removes head element of dll
   \param dll a dll
   \pre dll is not DLL_NULL
   \return new head of dll or DLL_NULL
   \remarks Constant type
   \remarks destructive for dll
   \author Pascal Fontaine */
Tdll      dll_remove(Tdll dll);

/**
   \brief removes last element of dll
   \param dll a dll
   \pre dll is not DLL_NULL
   \return new head of dll or DLL_NULL
   \remarks Constant time
   \remarks destructive for dll
   \author David Deharbe */
Tdll      dll_pop_back(Tdll dll);

/**
   \brief inverts dll
   \param dll a dll
   \pre dll is not DLL_NULL
   \return new head of dll or DLL_NULL
   \remarks O(length(dll))
   \remarks destructive for dll
   \author Pascal Fontaine */
Tdll      dll_rev(Tdll dll);

/**
   \brief merges two dlls
   \param dll1 a dll
   \param dll2 a dll
   \return new head of dll 
   \remarks dll2 is added at the end of dll1
   \remarks Constant time
   \remarks destructive for dll1 and dll2, used to form result
   \author Pascal Fontaine */
Tdll      dll_merge(Tdll dll1, Tdll dll2);

/**
   \brief reverts the effect of a merge
   \param dll1 a dll
   \param dll2 a dll
   \pre dll1 was attributed the result of dll_merge(dll1, dll2)
   \return head of dll1
   \remarks the effect of the call dll_merge(dll1, dll2) is reverted
   \remarks Constant time
   \remarks destructive for dll
   \author Pascal Fontaine */
Tdll      dll_anti_merge(Tdll dll1, Tdll dll2);

/**
   \brief Debugging function
   \param dll a dll
   \return 1 if dll is consistent (i.e. correctly doubly-linked), 0
   otherwise.
   \author Pascal Fontaine */
int       dll_consistency(Tdll dll);

/**
   \brief Applies a function to all elements of a dll
   \param dll a dll
   \param f a function
   \post f has been applied to each element of dll, in order
   \remarks Lin time % length of dll (assuming cost of calling f is constant)
   \author Pascal Fontaine */
void      dll_apply(Tdll dll, void (*f) (GEN_TYPE));

/**
   \brief Filters element in a dll
   \param dll a dll
   \param pred a test function
   \return returns a new dll of all elements satisfying pred
   \remarks Lin time % length of dll (assuming cost of calling pred is
   constant)
   \remarks non-destructive (assuming pred is side-effect free)
   \author Pascal Fontaine */
Tdll      dll_filter(Tdll dll, int (*pred) (GEN_TYPE));

/**
   \brief Filters a dll
   \param dll a dll
   \param pred a test function
   \return removes elements from dll satisfying pred
   \remarks Lin time % length of dll (assuming cost of calling pred is
   constant).
   \remarks destructive
   \author David Deharbe */
Tdll      dll_remove_all(Tdll dll, int (*pred) (GEN_TYPE));

/**
   \brief checks if a dll is a permutation of another
   \param dll1 a dll
   \param dll2 another dll
   \return 1 iff both dlls are the same
   \remarks Lin time % length of dll 
   \remarks non destructive
   \author Pascal Fontaine */
int       dll_same(Tdll dll1, Tdll dll2);

/**
   \brief initialize the module
   \author Pascal Fontaine */
void      dll_init(void);

/**
   \brief release the module
   \author Pascal Fontaine */
void      dll_done(void);

#endif /* __DLL_H */
