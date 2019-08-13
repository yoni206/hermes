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

/*
  --------------------------------------------------------------
  Module for doing structural recursion on DAGs
  --------------------------------------------------------------
*/

#ifndef __RECURSION_H
#define __RECURSION_H

#include "DAG.h"
#include "proof.h"

/**
   \author Pascal Fontaine
   \brief builds a new DAG by applying a function
   \param src the input DAG
   \param f a destructive function from DAG to DAG
   \return src in which f has been applied recursively from leaves to root
   \remarks Linear with the DAG size
   \remarks Uses flag
   \remarks Non destructive */
TDAG      structural_recursion(TDAG src, TDAG (*f) (TDAG));

/**
   \author Pascal Fontaine
   \brief builds new DAGs by applying a function.  The new DAGs are stored in
   the input array
   \param n the number of input DAGs
   \param Psrc the input DAGs
   \param f a destructive function from DAG to DAG
   \remarks Linear with the DAGs size
   \remarks Uses flag
   \remarks Destructive */
void      structural_recursion_array(unsigned n, TDAG * Psrc, TDAG (*f) (TDAG));

/**
   \author David Déharbe
   \brief builds a new DAG by applying a function while cont(DAG) is true
   \param src the input DAG
   \param f a destructive function from DAG to DAG
   \param cont a predicate on DAGs
   \return src in which f has been applied recursively while cont(DAG) is true
   \remarks Linear with the DAG size
   \remarks Uses flag
   \remarks Non destructive */
TDAG      cond_structural_recursion(TDAG src, TDAG (*f) (TDAG),
                                    bool (*cont) (TDAG));

/**
   \author David Déharbe
   \brief builds a new DAG by applying a function while cont(DAG) is true
   \param n the number of input DAGs
   \param Psrc the input DAGs
   \param f a destructive function from DAG to DAG
   \param cont a predicate on DAGs
   \return src in which f has been applied recursively while cont(DAG) is true
   \remarks Linear with the DAG size
   \remarks Uses flag
   \remarks Non destructive */
void      cond_structural_recursion_array(unsigned n, TDAG * Psrc,
                                          TDAG (*f) (TDAG), bool (*cont) (TDAG));

/**
   \author Pascal Fontaine
   \brief applies a predicate in a DAG
   \param src the input DAG
   \param f is a predicate on DAG node
   \return true if and only if f(N) is true for all nodes in src
   \remarks Linear with the DAG size
   \remarks Uses flag
   \remarks Non destructive */
bool      structural_recursion_pred(TDAG src, bool (*f) (TDAG));

/**
   \author Pascal Fontaine
   \brief applies f on every node of DAG
   \param src the input DAG
   \param f a void function on DAG node
   \remarks Linear with the DAG size
   \remarks Uses flag
   \remarks Non destructive */
void      structural_recursion_void(TDAG src, void (*f) (TDAG));

/*
   \author Pascal Fontaine
   \brief applies f on every node of DAG while cont(DAG) is true
   \param src the input DAG
   \param f a void function on DAG node
   \param cont a predicate on DAGs
   \remarks Linear with the DAG size
   \remarks Uses flag
   \remarks Non destructive */
void      cond_structural_recursion_void(TDAG src, void (*f) (TDAG),
                                         bool (*cont) (TDAG));

#endif /* __RECURSION_H */
