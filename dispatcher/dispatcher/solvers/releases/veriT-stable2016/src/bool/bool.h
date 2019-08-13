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
  Propositional Abstraction Module
  --------------------------------------------------------------
*/

#ifndef __BOOL_H
#define __BOOL_H

#include <stdio.h>

#include "config.h"

#include "stack.h"

#define INSIDE_VERIT
#include "veriT-SAT.h"
#include "DAG.h"
#include "literal.h"
#include "veriT-status.h"

#ifdef PROOF
#include "proof_id.h"
#endif

struct TSclause
{
  unsigned nb_lits;
#ifdef PROOF
  Tproof proof_id;
#endif
  Tlit    *lits;
};
typedef struct TSclause * Tclause;
TSstack(_clause, Tclause);

/* DD+PF creates a new clause, with place for nb_lits */
Tclause   clause_new(unsigned nb_lits);
/* DD+PF creates a new clause, with stack of lits */
Tclause   clause_new_stack(Tstack_lit lits);
/* PF creates a copy of clause */
Tclause   clause_dup(Tclause clause);
/* DD+PF set the i-th literal to argument */
void      clause_set_literal(Tclause clause, unsigned i, Tlit lit);
/* DD+PF allocate place for one supplementary literals, set it to arg */
void      clause_add_literal(Tclause clause, Tlit lit);
/* EB+PF creates a (cleaned) clause with all lits from the arguments */

/**
   \author Ezequiel Bazan and Pascal Fontaine
   creates a (cleaned) clause with all lits from the arguments
   \param clause1 first clause
   \param clause2 second clause
   \return the merged clause (clause1 OR clause2)
   \remarks Non destructive
   \remarks NULL list is represents TRUE
   \remarks A singleton with an empty clause represents FALSE */
Tclause   clause_merge(Tclause clause1, Tclause clause2);
/* PF removes repeated literals and sort; if valid returns NULL */
Tclause   clause_clean(Tclause clause);
/* PF tests if clauses are the same */
bool      clause_same(Tclause clause1, Tclause clause2);
/* DD+PF print clause in file */
void      clause_fprint(FILE * file, Tclause clause);
void      clause_free(Tclause clause);

#if 0
/**
   \author Pascal Fontaine
   \brief Tune the decision heuristics according to the formula */
void    bool_prepare(void);

/**
   \author David Déharbe and Pascal Fontaine
   \brief Check the set of formulas for a partial model
   \param level stop at decision level (0 if do not stop at level)  
   \param max_dec stop after max_dec decisions
   \return UNSAT, SAT, UNDEF
   \remark updates bool_model_Q, bool_model_size, bool_model_same, bool_model_constant, bool_model_complete */
Tstatus  bool_SAT_to_level(unsigned level, int max_dec);

/**
   \author David Déharbe and Pascal Fontaine
   \brief Check the set of formulas for a total model
   \return UNSAT, SAT
   \remark updates bool_model_Q, bool_model_size, bool_model_same, bool_model_constant, bool_model_complete */
int      bool_SAT(void);
#endif


/**
   \author David Déharbe and Pascal Fontaine
   \brief Add formula to the set of formulas to check for satisfiability
   \param formula the formula to add */
void     bool_add(TDAG formula);

#if PROOF
void     bool_add_proof(TDAG formula, Tproof proof);
#endif

/**
   \author David Déharbe and Pascal Fontaine
   \brief Add clause to the set of formulas to check for satisfiability
   \param clause the clause to add */
void     bool_add_c(Tclause clause);
/**
   \author David Déharbe and Pascal Fontaine
   \brief Add clause as conflict clause to the set of formulas to
   check for satisfiability
   \param clause the clause to add
   \remark the SAT solver may use the fact that clause is conflict clause */
void     bool_add_c_conflict(Tclause clause);
/**
   \author David Déharbe and Pascal Fontaine
   \brief Add clause as late explanation of hint
   \param clause the clause to add */
void     bool_add_c_hint(Tclause clause);

/**
   \author Pascal Fontaine
   \brief output cnf DIMACS of the abstraction of the formula
   \param filename name of file where CNF will be written to.
   \param status status of the set of formulas and clauses
   \param formulas table of formulas in the abstraction
   \param clauses table of clauses to add to the DIMACS file
   \remark use only at the end of normal work
   \remark it resets cnf module */
void     bool_recheck(char * filename, Tstatus status,
		      Tstack_DAG formulas, Tstack_clause clauses);

void     bool_reset(void);

void     bool_init(void);
void     bool_done(void);

/**
   \author Pascal Fontaine
   \brief get the decision level of literal */
unsigned bool_get_declev(Tlit lit);

/**
   \author Pascal Fontaine
   \brief Computes statistics on the module data */
void bool_stats_model(void);

#endif /* __BOOL_H */
