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
  Module responsible for DAG properties.

  A DAG may have properties. Property is an information that is (seldom)
  attached to some (and not all) DAGs.

  Each such property has a unique id. Properties are optional. They
  are used to implement SMT-LIB's formula annotations.  A new property
  may be created by supplying the size of the property value
  representation (in bytes) and a destructor function. The property
  value is ususally a pointer to some data structure that actually
  holds the interesting data.

  There are two pre-defined properties, identified as DAG_PROP_TRIGGER
  and DAG_PROP_NAMED.
*/

#ifndef DAG_PROP_H
#define DAG_PROP_H

#include "DAG.h"

/**
   \brief type for property identifiers
   \remark properties are stored in a stack and shall be used for
   rare attributes */
typedef unsigned Tprop_id;

/**
   \brief creates a property identifier
   \param f is the destructor for property values
   \param size the size of the property representation
   \return the property id */
extern Tprop_id DAG_prop_new(TFfree f, unsigned size);

/**
   \brief sets the value of a property
   \param DAG the DAG on which the property is set
   \param pid the identifier of the property
   \param value a pointer to its value */
extern void DAG_prop_set(TDAG DAG, Tprop_id pid, void * value);

/**
   \brief remove the value of a property
   \param DAG the DAG on which the property is removed
   \param pid the identifier of the property
   \return true on success */
extern bool DAG_prop_remove(TDAG DAG, Tprop_id pid);

/**
   \brief gets the value of a property
   \param DAG the DAG on which the property is read
   \param pid the identifier of the property
   \returns pointer to the address where the value of the property is assigned.
   \return 0 if property is not found, 1 otherwise */
extern void * DAG_prop_get(TDAG DAG, Tprop_id pid);

/**
   \brief check if there is a value for a property
   \param DAG the DAG on which the property is read
   \param pid the identifier of the property
   \return true on success */
extern bool DAG_prop_check(TDAG DAG, Tprop_id pid);

extern void DAG_prop_init(void);
extern void DAG_prop_done(void);

/** \brief trigger property (for quantified formulas) */
extern Tprop_id DAG_PROP_TRIGGER;
/** \brief The named property (for proofs and formulas) */
extern Tprop_id DAG_PROP_NAMED;

/** \brief NNF + Prenexed property (for quantified formulas). Only
    universals not under the scope of existentials are prenexed. */
extern Tprop_id  DAG_PROP_PNNF;
/** \brief cnf property (for quantified formulas) */
extern Tprop_id  DAG_PROP_CNF;
/** \brief possible instantiations property (for variables being unified) */
extern Tprop_id  DAG_PROP_INSTS;
/** \brief All function and predicate symbol occurrences in a DAG */
extern Tprop_id  DAG_PROP_SYMBS;
#endif
