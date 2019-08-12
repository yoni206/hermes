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

#ifndef __INST_PRE_H
#define __INST_PRE_H

#include "congruence.h"

/*
  --------------------------------------------------------------
  Preprocessing quantified formulas for instantiation
  --------------------------------------------------------------
*/



/*
  --------------------------------------------------------------
  Normal forms
  --------------------------------------------------------------
*/

/* [TODO] Should me merged into set_NFs */
/**
   \remark assumes tree structure (no "lets")
   \remark assumes DAG is in PNNF */
extern void set_CNF(TDAG DAG);

/**
   \brief computes prenexed NNF and CNF of quantified DAG with arbitrary boolean structure
   \param DAG a quantified formula
   \remark assumes tree structure (no "lets")

   \remark No miniscoping/Skolemization is done. Only prenex universal
   quantifiers not under the scope of existential ones. */
extern void set_NFs(TDAG DAG);

/**
    \author Haniel Barbosa

    \brief takes formula and for each quantifier occurrence puts it in prenexed
    NNF
    \param DAG a formula

    \remark Assumes no quantifier occurs

    \remark No miniscoping/Skolemization is done. Only prenex universal
    quantifiers not under the scope of existential ones.

    \remark Renames variables so that prenexing does not mess up univesal
    quantification. Does not account for existentials, so the latter may range
    over universally quantified variables (a subsequent call to qnt_tidy will be
    required then)

    \remark Not sure about how destructive it is */
extern TDAG qnt_NF(TDAG DAG);

extern TDAG qnt_connectives(TDAG DAG);
extern TDAG qnt_NNF(TDAG src);
extern TDAG qnt_uniq_vars(TDAG DAG);

/*
  --------------------------------------------------------------
  Triggers
  --------------------------------------------------------------
*/

/**
    \author David Deharbe, Pascal Fontaine, Haniel Barbosa
    \brief inspects the whole formula, adds trigger to every quantified formula
    without triggers, and ensures the triggers are on the formula itself, not on
    the body
    \param DAG the formula */
extern void set_triggers_old(TDAG DAG);

/**
    \author Haniel Barbosa

    \brief computes triggers for a (universally) quantified formula and its
    quantified subformulas

    \param DAG a formula
    \param previous_vars variables from previous quantifiers
    \param triggers accumulates triggers found in nested quantifiers

    \remark assumes that DAG is in NNF and that no variable is bound by more
    than one quantifier (stronger than ca pture, as it does not require that the
    variable be under the scope of those quantifiers) */
extern void
set_triggers(TDAG DAG, Tstack_DAG trigger_vars, Tstack_DAGstack * triggers);

/**
    \author Haniel Barbosa

    \brief computes nested triggers for a (universally) quantified formula and its
    quantified subformulas

    \param DAG a formula
    \param previous_vars variables from previous quantifiers
    \param triggers accumulates triggers found in nested quantifiers

    \remark assumes that DAG is in NNF and that no variable is bound by more
    than one quantifier (stronger than ca pture, as it does not require that the
    variable be under the scope of those quantifiers) */
extern void
set_nested_triggers(TDAG DAG, Tstack_DAG previous_vars,
                    Tstack_DAGstack * triggers);

/** Should disappear */
extern void inst_pre(TDAG src);

/*
  --------------------------------------------------------------
  Symbols
  --------------------------------------------------------------
*/

#endif
