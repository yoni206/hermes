/* -*- mode: C -*- */

/**
   \file Lists for TYPE
   \brief The module provides circular doubly-linked list (dll) for TYPE
   \author David Deharbe
   \author Pascal Fontaine */

/* Obtained using
   sed "s/\([^_]\)TY""PE/\1TYPE/g;s/E""XT/EXT/g;s/\"\"//g" dll-TY""PE.tpl > dll-EXT.h */

#ifndef __DLL_EXT_H
#define __DLL_EXT_H

#include "dll.h"

typedef Tdll Tdll_EXT;

#define DLL_EXT_NULL 0

/**
   \brief Constructor for dll with arguments in it.
   \param data a data of TYPE, followed by any number of TYPE datas
   \remarks Last argument should be 0 (TYPE)
   \return A dll containing the datas given as arguments, in the same order
   \author Pascal Fontaine */
#define dll_EXT_new_args(data, ...) dll_new_args((GEN_TYPE) data, __VA_ARGS__) 

/**
   \brief dll destructor
   \param Pdll address of the destructed list
   \post  Pdll is DLL_NULL
   \author Pascal Fontaine */
#define dll_EXT_free dll_free

/**
   \brief Accessor to first element
   \param dll a dll
   \pre dll is not DLL_NULL
   \return the first element of dll
   \author Pascal Fontaine */
#define dll_EXT_car(A) ((TYPE) dll_car(A))

/**
   \brief Accessor to last element
   \param dll a dll
   \pre dll is not DLL_NULL
   \return the last element of dll
   \author Pascal Fontaine */
#define dll_EXT_last(A) ((TYPE) dll_last(dll))

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
#define dll_EXT_cdr dll_cdr

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
#define dll_EXT_prev dll_prev

/**
   \brief Length of dll
   \param dll a dll
   \return the number of elements in dll
   \remarks Linear time.
   \author Pascal Fontaine */
#define dll_EXT_length dll_length

/**
   \brief dll copy
   \param dll a dll
   \return a copy of dll, the order is preserved
   \remark Linear time
   \author Pascal Fontaine */
#define dll_EXT_cpy dll_cpy

/**
   \brief Creates a dll with a single element
   \param data a data
   \return dll containing single element data
   \remarks Constant time */
#define dll_EXT_one(A) dll_one((GEN_TYPE) data)

/**
   \brief Adds element to head of dll
   \param data a data
   \param dll a dll
   \return dll with head containing data and tail equal to dll.
   \remarks Constant time
   \remarks destructive for dll */
#define dll_EXT_cons(data, dll) dll_cons((GEN_TYPE) data, dll)

/**
   \brief Adds element to tail of dll
   \param data a data
   \param dll a dll
   \return dll with elements of argument followed by data
   \remarks Constant time
   \remarks destructive for dll */
#define dll_EXT_add(dll, data) dll_add(dll, (GEN_TYPE) data)

/**
   \brief Replace by P first element of dll.
   \param dll a dll
   \param data a data
   \return dll with elements of argument dll, but data instead of first element
   \remarks The argument is modified in place and returned
   \remarks Constant time
   \remarks destructive for dll */
#define dll_set_car(dll, data) dll_set_car(dll, (GEN_TYPE) data)

/**
   \brief accessor based on position
   \param dll a dll
   \param n a position
   \return element at position n of dll if it exists, 0 otherwise
   \remark O(n) */
#define dll_EXT_n(dll, n) ((TYPE) dll_n(dll, n))

/**
   \brief removes head element of dll
   \param dll a dll
   \pre dll is not DLL_NULL
   \return new head of dll or DLL_NULL
   \remarks Constant type
   \remarks destructive for dll
   \author Pascal Fontaine */
#define dll_EXT_remove dll_remove

/**
   \brief removes last element of dll
   \param dll a dll
   \pre dll is not DLL_NULL
   \return new head of dll or DLL_NULL
   \remarks Constant time
   \remarks destructive for dll
   \author David Deharbe */
#define dll_EXT_pop_back dll_pop_back

/**
   \brief inverts dll
   \param dll a dll
   \pre dll is not DLL_NULL
   \return new head of dll or DLL_NULL
   \remarks O(length(dll))
   \remarks destructive for dll
   \author Pascal Fontaine */
#define dll_EXT_rev dll_rev

/**
   \brief merges two dlls
   \param dll1 a dll
   \param dll2 a dll
   \return new head of dll 
   \remarks dll2 is added at the end of dll1
   \remarks Constant time
   \remarks destructive for dll1 and dll2, used to form result
   \author Pascal Fontaine */
#define dll_EXT_merge dll_merge

/**
   \brief reverts the effect of a merge
   \param dll dll
   \pre dll was attributed the result of dll_merge(dll1, dll2)
   \return head of dll1
   \remarks the effect of the call dll_merge(dll1, dll2) is reverted
   \remarks Constant time
   \remarks destructive for dll
   \author Pascal Fontaine */
#define dll_EXT_anti_merge dll_anti_merge

/**
   \brief Debugging function
   \param dll a dll
   \return 1 if dll is consistent (i.e. correctly doubly-linked), 0
   otherwise.
   \author Pascal Fontaine */
#define dll_EXT_consistency dll_consistency

/**
   \brief Applies a function to all elements of a dll
   \param dll a dll
   \param f a function
   \post f has been applied to each element of dll, in order
   \remarks Lin time % length of dll (assuming cost of calling f is constant)
   \author Pascal Fontaine */
#define dll_EXT_apply(dll, f) (dll, (TFapply) f)

/**
   \brief Filters element in a dll
   \param dll a dll
   \param pred a test function
   \return returns a new dll of all elements satisfying pred
   \remarks Lin time % length of dll (assuming cost of calling pred is
   constant)
   \remarks non-destructive (assuming pred is side-effect free)
   \author Pascal Fontaine */
#define dll_EXT_filter(dll, pred) dll_filter(dll, (TFtest) pred)

/**
   \brief Filters a dll
   \param dll a dll
   \param pred a test function
   \return removes elements from dll satisfying pred
   \remarks Lin time % length of dll (assuming cost of calling pred is
   constant).
   \remarks destructive
   \author David Deharbe */
#define dll_EXT_remove_all(dll, pred) dll_remove_all(dll, (TFtest) pred)

/**
   \brief checks if a dll is a permutation of another
   \param dll1 a dll
   \param dll2 another dll
   \return 1 iff both dlls are the same
   \remarks Lin time % length of dll 
   \remarks non destructive
   \author Pascal Fontaine */
#define dll_EXT_same dll_same

#endif /* __DLL_H */
