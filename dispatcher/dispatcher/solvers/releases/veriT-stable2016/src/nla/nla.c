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

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "config.h"

#include "DAG-arith.h"
#include "bool.h"
#include "congruence.h"
#include "veriT-state.h"
#include "veriT-status.h"
#include "veriT-DAG.h"
#include "reduce.h"
#include "veriT-signal.h"

#ifdef PROOF
#include "proof.h"
#endif

#ifdef DEBUG
#include "options.h"
#endif

#include "nla.h"

/* #define DEBUG_NLA */

#define UNSAT_CORE

/*--------------------------------------------------------------*/

typedef struct Tto_redlog {
  enum {
    TYPE_DAG,
    TYPE_LIT_POS,
    TYPE_LIT_NEG
  } type;
  TDAG DAG;
} Tto_redlog;

TSstack(_to_redlog,Tto_redlog);

static Tstack_to_redlog to_redlog;
static Tstack_lit input_literals;

static Tstatus NLA_status = UNDEF;

#ifdef UNSAT_CORE 
static Tstack_lit unsat_core_ids;
#endif 

static int litFalse;
static int litFalseIx;

/*--------------------------------------------------------------*/

#ifdef DEBUG
/**
   \addtogroup arguments_developer

   - --redlog-log

   Generates files in redlog format with the formula given to it
   during nla reasoning. Useful to debug nla (only available
   when compiled with DEBUG defined). */
bool redlog_log = false;

/**
   \addtogroup arguments_developer

   - --redlog-smt2-log

   Generates files in SMT2 format with the formula given to redlog
   Useful to debug nla (only available
   when compiled with DEBUG defined). */
bool redlog_smt2_log = false;

static FILE *f_red = NULL;
static FILE *f_smt2 = NULL;
TSstack(_str, char *);
static Tstack_str DAGs_already_defined = NULL;
#endif

/*
  --------------------------------------------------------------
  Redlog interaction
  --------------------------------------------------------------
*/

char * reduce_path = NULL;

static RedProc redlog_process;
static char * redlog_output = NULL;

/*--------------------------------------------------------------*/

static inline void
redlog_check(void)
{
  FILE * file;
  if (reduce_path && (file = fopen(reduce_path, "r")))
    {
      fclose(file);
      return;
    }
  my_error("No reduce executable found\n"
	   "Please export in VERIT_REDUCE_PATH the full path to redpsl\n");
}

/*--------------------------------------------------------------*/

static inline void
redlog_init(void)
{
  redlog_process = RedProc_new(reduce_path);
}

/*--------------------------------------------------------------*/

static inline void
redlog_done(void)
{
  free(redlog_output);
  redlog_output = NULL;
  RedProc_delete(redlog_process);
}

/*--------------------------------------------------------------*/

static inline void
redlog_command(char * command)
{
  RedAns output = RedAns_new(redlog_process, command);
#ifdef DEBUG
  if (redlog_log && f_red)
    fprintf(f_red, "%s\n", command);
  if (redlog_smt2_log && f_smt2)
    fprintf(f_smt2, "%s\n", command);
#endif
#ifdef DEBUG_NLA
  my_message("Command: %s\n", command);
#endif
  free(redlog_output);
  redlog_output = NULL;
  if (output->error)
    {
      RedProc_error(redlog_process, command, output);
      RedProc_delete(redlog_process);
      exit(-1);
    }
  redlog_output = strmake(output->result);

#ifdef UNSAT_CORE  
  if (output->pretext != NULL &&
      strstr(strmake(output->pretext), strmake("infcore:")) != NULL)
    {
      char *token, *state;
      char *es, *ee;
      char *ls, *le;
      int ind_start, ind_end;
      char *st = strmake(output->pretext);
      unsigned len;

#ifdef DEBUG_NLA
      my_message("Unsat core: %s\n", st);
#endif
      stack_reset(unsat_core_ids);
      
      es = strchr(st, '(')+1;
      ee = strchr(st, ')');
      ind_start = (int)(es - st);
      ind_end = (int)(ee - st);
        
      len = ind_end - ind_start;
      char core_ids[len+1]; 
      strncpy(core_ids, st + ind_start, len);
      core_ids[len] = '\0';

      ls = strstr(st, "input length:") + 14;
      le = strchr(st, '\0');
 
      char input_len[le - ls + 1]; 

      strncpy(input_len, ls, le - ls);

      input_len[le - ls + 1] = '\0';

      /*printf("\n--------------------------\n");*/
      int input_len_i = atoi(input_len);
      
      for (token = strtok_r(core_ids, " \n", &state);
           token != NULL; token = strtok_r(NULL, " \n", &state))
        {
          int idRed = atoi(strmake(token)); 
          int idVeriT = input_len_i - idRed -1;
          /* printf("idRedlog [%d] ok [%d]\n", idRed, idVeriT); */
          stack_push(unsat_core_ids, idVeriT);      
        }
      /*printf("TOKEN [%s]\n", strmake(token));
	exit(0);*/      
    }
#endif

#ifdef DEBUG_NLA
  printf("Output: %s\n", output->result);
#endif
  RedAns_delete(output);
}

/*
  --------------------------------------------------------------
  Output functions
  --------------------------------------------------------------
*/

static unsigned redlog_buffer_size = 0;
static unsigned redlog_buffer_p = 0;
static char * redlog_buffer = NULL;

static void
redlog_buffer_add(char *str)
{
  unsigned size = (unsigned) strlen(str) + 1;
  if (redlog_buffer_p + size >= redlog_buffer_size)
    {
      while (redlog_buffer_p + size >= redlog_buffer_size)
	{
	  redlog_buffer_size *= 2;
	  MY_REALLOC(redlog_buffer, redlog_buffer_size);
	}
    }
  strcpy(redlog_buffer + redlog_buffer_p, str);
  redlog_buffer_p += size - 1;
}

/*--------------------------------------------------------------*/

static void
redlog_buffer_clean(void)
{
  redlog_buffer_p = 0;
  redlog_buffer[0] = 0;
}

/*
  --------------------------------------------------------------
  DAG to redlog
  --------------------------------------------------------------
*/

static Tstack_DAG DAG_todo;

/*--------------------------------------------------------------*/

/**
   \brief accumulates all monoms in DAG
   \param DAG a DAG
   \remark if term is not a linear term, introduce a variable for it and adds
   its subterms for deep inspection */
static void
NLA_notify_term(TDAG DAG)
{
  unsigned i;
  char *str;
  Tsymb symb = DAG_symb(DAG);
  if (symb == FUNCTION_SUM ||
      symb == FUNCTION_PROD ||
      symb == FUNCTION_UNARY_MINUS ||
      symb == FUNCTION_UNARY_MINUS_ALT ||
      symb == FUNCTION_MINUS ||
      symb == FUNCTION_DIV)
    { 
      redlog_buffer_add("(");
      redlog_buffer_add(DAG_symb_name2(symb));
      for (i = 0; i < DAG_arity(DAG); i++)
	{
	  redlog_buffer_add(" ");
	  NLA_notify_term(DAG_arg(DAG, i));
	}
      redlog_buffer_add(")");
      return;
    }
  if (DAG_is_number(DAG))
    {         
      char * tmp = DAG_number_str(DAG);
      redlog_buffer_add(tmp);
      return;
    }
  MY_MALLOC(str, 20 * sizeof(char));
  snprintf(str, 20, "v%d", CC_abstract(DAG));
#ifdef DEBUG
  if (redlog_smt2_log)
    {
      unsigned i;
      int already_defined = 0;
      for (i = 0; i < stack_size(DAGs_already_defined); i++)
	if (!strcmp(str, stack_get(DAGs_already_defined, i)))
	  already_defined = 1;
      if (!already_defined)
        {
          stack_push(DAGs_already_defined, strmake(str));
          if (f_smt2)
            fprintf(f_smt2, "(declare-fun %s () Real)\n", str);
        }
    }
#endif
  redlog_buffer_add(str);
  free(str);
  if (DAG_arity(DAG))
    for (i = 0; i < DAG_arity(DAG); i++)
      stack_push(DAG_todo, DAG_arg(DAG,i));
}

/*--------------------------------------------------------------*/

/**
   \brief introduces arithmetic definition for all arithmetic subterms in DAG
   \param DAG a DAG */
static void
NLA_notify_deep_terms(TDAG DAG)
{
  unsigned i;
  char *str;
  Tsymb symb = DAG_symb(DAG);
#ifdef DEBUG_NLA
  my_DAG_message("NLA_notify_deep_terms: %D\n", DAG);
#endif
  if (symb == FUNCTION_SUM ||
      symb == FUNCTION_PROD ||
      symb == FUNCTION_UNARY_MINUS ||
      symb == FUNCTION_UNARY_MINUS_ALT ||
      symb == FUNCTION_MINUS ||
      symb == FUNCTION_DIV)
    { 
      stack_inc(to_redlog);
      stack_top(to_redlog).type = TYPE_DAG;
      stack_top(to_redlog).DAG = DAG;
      redlog_buffer_add("(assert (= ");
      MY_MALLOC(str, 20 * sizeof(char));
      snprintf(str, 20, "v%d", CC_abstract(DAG));
      redlog_buffer_add(str);
      free(str);
      redlog_buffer_add(" (");
      redlog_buffer_add(DAG_symb_name2(symb));
      for (i = 0; i < DAG_arity(DAG); i++)
	{
	  redlog_buffer_add(" ");
	  NLA_notify_term(DAG_arg(DAG, i));
	}
      redlog_buffer_add(")))");
      redlog_command(redlog_buffer);
      redlog_buffer_clean();
      return;
    }
  if (DAG_is_number(DAG))
    { 
      char * tmp = DAG_number_str(DAG);
      redlog_buffer_add("(assert (= ");
      MY_MALLOC(str, 20 * sizeof(char));
      snprintf(str, 20, "v%d", CC_abstract(DAG));
      redlog_buffer_add(str);
      free(str);
      redlog_buffer_add(" ");
      redlog_buffer_add(tmp);
      free(tmp);
      redlog_buffer_add("))");
      redlog_command(redlog_buffer);
      redlog_buffer_clean();
      return;
    }
  for (i = 0; i < DAG_arity(DAG); i++)
    NLA_notify_deep_terms(DAG_arg(DAG,i));
}

/*--------------------------------------------------------------*/

/**
   \brief stores arithmetic definition for the atom,
   and all arithmetic terms in DAG
   \param DAG a DAG
   \param pol the polarity of DAG */
static inline void
NLA_notify_atom(TDAG DAG, int pol)
{
  if (DAG_symb(DAG) == PREDICATE_LESS ||
      DAG_symb(DAG) == PREDICATE_LEQ ||
      DAG_symb(DAG) == PREDICATE_GREATER ||
      DAG_symb(DAG) == PREDICATE_GREATEREQ ||
      DAG_symb(DAG) == PREDICATE_EQ)
    {
      stack_inc(to_redlog);
      stack_top(to_redlog).DAG = DAG;
      stack_top(to_redlog).type = pol?TYPE_LIT_POS:TYPE_LIT_NEG;
      redlog_buffer_add(pol?"(assert ":"(assert (not ");
      redlog_buffer_add("(");
      redlog_buffer_add(DAG_symb_name2(DAG_symb(DAG)));
      redlog_buffer_add(" ");
      NLA_notify_term(DAG_arg0(DAG));
      redlog_buffer_add(" ");
      NLA_notify_term(DAG_arg1(DAG));
      redlog_buffer_add(")");
      redlog_buffer_add(pol?")":"))");
      redlog_command(redlog_buffer);
      redlog_buffer_clean();
    }
  else if (DAG_symb(DAG) == PREDICATE_ISINT)
    my_error("DAG2LA: not implemented\n");
  else if (DAG_symb_type(DAG_symb(DAG)) | SYMB_QUANTIFIER)
    return;
  else
    {
      unsigned i;
      for (i = 0; i < DAG_arity(DAG); i++)
	stack_push(DAG_todo, DAG_arg(DAG, i));
    }
  while (stack_size(DAG_todo))
    NLA_notify_deep_terms(stack_pop(DAG_todo));
}

/*--------------------------------------------------------------*/

/**
   \brief accumulates all monoms in DAG
   \param DAG a DAG
   \remark if term is not a linear term, introduce a variable for it and adds
   its subterms for deep inspection */
static void
NLA_collect_vars(TDAG DAG, Tstack_DAG * Pstack_vars)
{
  unsigned i;
  Tsymb symb = DAG_symb(DAG);
  if (symb == FUNCTION_SUM ||
      symb == FUNCTION_PROD ||
      symb == FUNCTION_UNARY_MINUS ||
      symb == FUNCTION_UNARY_MINUS_ALT ||
      symb == FUNCTION_MINUS ||
      symb == FUNCTION_DIV)
    for (i = 0; i < DAG_arity(DAG); i++)
      NLA_collect_vars(DAG_arg(DAG, i), Pstack_vars);
  if (DAG_is_number(DAG))
    return;
  stack_push(*Pstack_vars, DAG);
  if (DAG_arity(DAG))
    for (i = 0; i < DAG_arity(DAG); i++)
      stack_push(DAG_todo, DAG_arg(DAG,i));
}

/*--------------------------------------------------------------*/

/**
   \brief introduces arithmetic definition for all arithmetic subterms in DAG
   \param DAG a DAG */
static void
NLA_collect_vars_deep(TDAG DAG, Tstack_DAG * Pstack_vars)
{
  unsigned i;
  Tsymb symb = DAG_symb(DAG);
  if (symb == FUNCTION_SUM ||
      symb == FUNCTION_PROD ||
      symb == FUNCTION_UNARY_MINUS ||
      symb == FUNCTION_UNARY_MINUS_ALT ||
      symb == FUNCTION_MINUS ||
      symb == FUNCTION_DIV ||
      DAG_is_number(DAG))
    {
      stack_push(*Pstack_vars, DAG);
      for (i = 0; i < DAG_arity(DAG); i++)
        {
          redlog_buffer_add(" ");
          NLA_collect_vars(DAG_arg(DAG, i), Pstack_vars);
        }
      return;
    }
  for (i = 0; i < DAG_arity(DAG); i++)
    NLA_collect_vars_deep(DAG_arg(DAG,i), Pstack_vars);
}

/*--------------------------------------------------------------*/

/**
   \brief stores arithmetic definition for the atom,
   and all arithmetic terms in DAG
   \param DAG a DAG
   \param pol the polarity of DAG */
static inline void
NLA_collect_vars_atom(TDAG DAG, Tstack_DAG * Pstack_vars)
{
  if (DAG_symb(DAG) == PREDICATE_LESS ||
      DAG_symb(DAG) == PREDICATE_LEQ ||
      DAG_symb(DAG) == PREDICATE_GREATER ||
      DAG_symb(DAG) == PREDICATE_GREATEREQ ||
      DAG_symb(DAG) == PREDICATE_EQ)
    {
      NLA_collect_vars(DAG_arg0(DAG), Pstack_vars);
      NLA_collect_vars(DAG_arg1(DAG), Pstack_vars);
    }
  else if (DAG_symb(DAG) == PREDICATE_ISINT)
    my_error("DAG2LA: not implemented\n");
  else if (DAG_symb_type(DAG_symb(DAG)) | SYMB_QUANTIFIER)
    return;
  else
    {
      unsigned i;
      for (i = 0; i < DAG_arity(DAG); i++)
	stack_push(DAG_todo, DAG_arg(DAG, i));
    }
  while (stack_size(DAG_todo))
    NLA_collect_vars_deep(stack_pop(DAG_todo), Pstack_vars);
}

#if 0

/*--------------------------------------------------------------*/

void
DAG_to_redlog_term(TDAG DAG)
{
  unsigned i;
  if (DAG_arity(DAG) == 0)
    {
      redlog_buffer_add(DAG_symb_name(DAG_symb(DAG)));
      return;
    }
  redlog_buffer_add("(");
  if (DAG_symb(DAG) == FUNCTION_SUM)
    redlog_buffer_add("+");
  else if (DAG_symb(DAG) == FUNCTION_UNARY_MINUS)
    {
      assert(DAG_arity(DAG) == 1);
      redlog_buffer_add("-");
    }
  else if (DAG_symb(DAG) == FUNCTION_MINUS)
    {
      assert(DAG_arity(DAG) == 2);
      redlog_buffer_add("-");
    }
  else if (DAG_symb(DAG) == FUNCTION_PROD)
    redlog_buffer_add("*");
  else
    my_error("unrecognized symbol\n");
  /* fprintf(file, "(%s", DAG_symb_name(DAG_symb(DAG)));*/
  for (i = 0; i < DAG_arity(DAG); i++)
    {
      redlog_buffer_add(" ");
      DAG_to_redlog_term(DAG_arg(DAG, i));
    }
  redlog_buffer_add(")");
}

/*--------------------------------------------------------------*/

static inline void
DAG_to_redlog_deep_term(TDAG DAG)
{
}

/*--------------------------------------------------------------*/

static inline void
DAG_to_redlog_atom(TDAG DAG, bool pol)
{
  unsigned i;
  /* Ignore propositional variables */
  if (DAG_arity(DAG) == 0)
    return;
  if (DAG_symb(DAG) == PREDICATE_LESS ||
      DAG_symb(DAG) == PREDICATE_LEQ ||
      DAG_symb(DAG) == PREDICATE_GREATEREQ || /* TODO Rename to GEQ */
      DAG_symb(DAG) == PREDICATE_GREATER)
    {
      redlog_buffer_add(pol?"(":"(not (");
      redlog_buffer_add(DAG_symb_name(DAG_symb(DAG)));
      redlog_buffer_add(" ");
      DAG_to_redlog_term(DAG_arg0(DAG));
      redlog_buffer_add(" ");
      DAG_to_redlog_term(DAG_arg1(DAG));
      redlog_buffer_add(pol?")":"))");
      return;
    }
  my_error("unrecognized symbol\n");
}

#endif

/*
  --------------------------------------------------------------
  Public functions
  --------------------------------------------------------------
*/

static inline void
redlog_exit(void)
{
  if (!redlog_buffer_size)
    return;
  RedProc_delete(redlog_process);
}

/*--------------------------------------------------------------*/

void
NLA_init(void)
{
  redlog_buffer_size = 0;
  redlog_buffer_p = 0;
  veriT_signal_register(&redlog_exit);
#ifdef DEBUG
  options_new(0, "redlog-log",
	      "Produce REDLOG formulas during NLA reasoning.  "
	      "Useful for debugging", &redlog_log);
  options_new(0, "redlog-smt2-log",
	      "Produce REDLOG formulas during NLA reasoning in SMT2 format.  "
	      "Useful for debugging", &redlog_smt2_log);
  stack_INIT(DAGs_already_defined);
#endif
}

/*--------------------------------------------------------------*/

void
NLA_done(void)
{
  if (!redlog_buffer_size)
    return;
  redlog_command("(exit)");
  redlog_done();
  stack_free(DAG_todo);
  stack_free(input_literals);
  stack_free(to_redlog);
#ifdef UNSAT_CORE 
  stack_free(unsat_core_ids);
#endif
  free(redlog_buffer);
  redlog_buffer = NULL;
  redlog_buffer_size = 0;
  redlog_buffer_p = 0;
#ifdef DEBUG
  if (redlog_smt2_log)
    {
      unsigned i;
      for (i = 0; i < stack_size(DAGs_already_defined); i++)
	free(stack_get(DAGs_already_defined, i));
      stack_free(DAGs_already_defined);
    }
#endif
}

/*--------------------------------------------------------------*/

void
NLA_activate(void)
{
  redlog_check();
  stack_INIT(input_literals);
  stack_INIT(to_redlog);
#ifdef UNSAT_CORE
  stack_INIT(unsat_core_ids);
#endif  
  stack_INIT(DAG_todo);
  redlog_buffer_size = 256;
  MY_MALLOC(redlog_buffer, redlog_buffer_size * sizeof(char));
  redlog_init();
  redlog_command("smts_mainloop();");
  redlog_command("(set-logic QF_NRA)");
}

/*--------------------------------------------------------------*/

Tstatus
NLA_assert(Tlit lit)
{
  stack_push(input_literals, lit);
  return NLA_status;
}

/*--------------------------------------------------------------*/

void
NLA_clear(void)
{
  NLA_status = UNDEF;
  stack_reset(input_literals);
  stack_reset(to_redlog);
#ifdef UNSAT_CORE  
  stack_reset(unsat_core_ids);
#endif
}

/*--------------------------------------------------------------*/

Tstatus
NLA_solve(void)
{
  unsigned i;
  Tlit lit;
  TDAG DAG;
#ifdef DEBUG
  static unsigned nb = 1;
  static unsigned nb_smt2 = 1;
#endif
  redlog_buffer_clean();
  if (!stack_size(input_literals))    
    return SAT;
  redlog_command("(reset)");

  static int nb_calls = 0;
  /*printf("NB calls redlog [%d]\n", ++nb_calls);
    printf("(check-sat)\n");
  redlog_command("(check-sat)");*/
  /*printf("\t return\n");*/
  if (nb_calls > 500)
    {
      nb_calls = 0;
      //redlog_exit();
      redlog_done();

      redlog_init();
      //exit(0);
      redlog_command("smts_mainloop();");
      redlog_command("(set-logic QF_NRA)");      
    }

#ifdef DEBUG
  if (redlog_log)
    {
      char filename[128];
      sprintf(filename, "reduce_%05d.red", nb++);
      f_red = fopen(filename, "w");
      fprintf(f_red, "smt();\n");
      fprintf(f_red, "(set-logic QF_NRA)\n");
    }
  if (redlog_smt2_log)
    {
      char smtfilename[128];
      sprintf(smtfilename, "reduce_%05d.smt2", nb_smt2++);
      f_smt2 = fopen(smtfilename, "w");
      fprintf(f_smt2, "(set-logic QF_NRA)\n");
    }
#endif
  litFalseIx = -1;
  for (i = 0; i < stack_size(input_literals); ++i)
    {
      litFalse = 0;
      lit = stack_get(input_literals, i);
      if (!lit)
	continue;
      DAG = var_to_DAG(lit_var(lit));
      assert(DAG);
      NLA_notify_atom(DAG, lit_pol(lit));
    }
#ifdef DEBUG
  if (redlog_log && f_red)
    {
      fprintf(f_red, "(check-sat)\n");
      fclose(f_red);
      f_red = NULL;
    }
  if (redlog_smt2_log && f_smt2)
    {
      unsigned i;
      fprintf(f_smt2, "(check-sat)\n");
      fclose(f_smt2);
      f_smt2 = NULL;
      for (i = 0; i < stack_size(DAGs_already_defined); i++)
	free(stack_get(DAGs_already_defined, i));
      stack_free(DAGs_already_defined);
      stack_INIT(DAGs_already_defined);
    }
#endif
  redlog_command("(check-sat)");
#ifdef DEBUG_NLA
  my_message("NLA_solve: %s\n", redlog_output); 
#endif
  if (!strcmp(redlog_output, "sat"))
    return NLA_status = SAT;
  if (!strcmp(redlog_output, "unsat"))
    return NLA_status = UNSAT;
  if (!strcmp(redlog_output, "unknown"))
    return NLA_status = UNDEF;
  my_error("NLA_solve: unexpected result\n");
  return UNDEF;
}

/*--------------------------------------------------------------*/

static int
comp_CC_abstract(TDAG * PDAG1, TDAG * PDAG2)
{
  return ((int)CC_abstract(*PDAG1)) - ((int)CC_abstract(*PDAG2));
}

#ifdef UNSAT_CORE
void
NLA_conflict(void)
{
  unsigned i;
  Tstack_DAG DAGs = NULL;
  assert(NLA_status == UNSAT);
#ifdef DEBUG_NLA
  my_message("NLA conflict [%d]/[%d]\n", stack_size(unsat_core_ids),
    stack_size(input_literals));
#endif
  stack_INIT(DAGs);
  for (i = 0; i < stack_size(unsat_core_ids); ++i)
    {
      Tlit lit;
      if (stack_get(to_redlog, stack_get(unsat_core_ids, i)).type ==
          TYPE_DAG)
        {
          NLA_collect_vars_atom(stack_get(to_redlog,
                                          stack_get(unsat_core_ids, i)).DAG, &DAGs);
          continue;
        }
      lit = DAG_to_lit(stack_get(to_redlog, stack_get(unsat_core_ids, i)).DAG);
      if (stack_get(to_redlog, stack_get(unsat_core_ids, i)).type == TYPE_LIT_NEG)
        lit = lit_neg(lit);;
#ifdef DEBUG_NLA
      my_DAG_message("lit %d %D\n", lit,
                     stack_get(to_redlog, stack_get(unsat_core_ids, i)).DAG);
#endif
      stack_push(veriT_conflict, lit);
      NLA_collect_vars_atom(lit_to_DAG(lit), &DAGs);
    }
  stack_sort(DAGs, comp_CC_abstract);
  for (i = 1; i < stack_size(DAGs); i++)
    if (CC_abstract(stack_get(DAGs, i - 1)) == CC_abstract(stack_get(DAGs, i)))
      {
        stack_push(veriT_conflict_eqs, stack_get(DAGs, i - 1));
        stack_push(veriT_conflict_eqs, stack_get(DAGs, i));
      }
}
#else
void
NLA_conflict(void)
{
  /*printf("\tCONFLICT\n");*/
  Tlit lit;
  unsigned i;
  assert(NLA_status == UNSAT);
  for (i = 0; i < stack_size(input_literals); ++i)
    {
      lit = stack_get(input_literals, i);
      if (!lit)
	continue;
      stack_push(veriT_conflict, lit);
    }
}
#endif

/*--------------------------------------------------------------*/

#ifdef PROOF
Tproof
NLA_conflict_proof(void)
{
  Tstack_DAG lits;
  unsigned i;
  Tproof proof;
  assert(NLA_status == UNSAT);
  stack_INIT(lits);
#ifdef UNSAT_CORE
  for (i = 0; i < stack_size(unsat_core_ids); ++i)
    {
      Tlit lit = stack_get(input_literals, stack_get(unsat_core_ids, i));
#else
  for (i = 0; i < stack_size(input_literals); ++i)
    {
      Tlit lit = stack_get(input_literals, i);
#endif

      TDAG DAG = lit_to_DAG(lit);
      if (!lit)
	continue;
      stack_push(veriT_conflict, lit);
      stack_push(lits, DAG_dup(lit_pol(lit)?DAG_not(DAG):DAG));
    }
  proof = proof_clause_stack(nla_generic, lits);
  stack_apply(lits, DAG_free);
  stack_free(lits);
  return proof;
}
#endif

/*--------------------------------------------------------------*/

bool
NLA_has_lemma(void)
{
  return false;
}

/*--------------------------------------------------------------*/

TSstack(_stack_DAG, Tstack_DAG);

#define eat_spaces() do { while (redlog_output[i] && redlog_output[i] == ' ') i++; } while (0)
#define jump_end_id() do { while (redlog_output[i] && redlog_output[i] != ' ' && redlog_output[i] != ')') i++; } while (0)


/*--------------------------------------------------------------*/

bool
NLA_model_eq(void)
{
  unsigned i, j = 0;
  Tstack_stack_DAG partition;
  unsigned counter = 0;
  assert(NLA_status != UNSAT);
  if (NLA_status == UNDEF)
    return false;
  stack_INIT(partition);
  redlog_command("(get-model)");
  for (i = 0; redlog_output[i]; i++)
    if (redlog_output[i] == '\n')
      redlog_output[i] = ' ';
  if (redlog_output[0])
    for (i = 1, j = 0; redlog_output[i]; i++)
      if (redlog_output[i] != ' ' || redlog_output[j] != ' ')
	redlog_output[++j] = redlog_output[i];
  redlog_output[++j] = 0;
  i = 0;
  assert(redlog_output[i] == '(');
  i++;
  while (redlog_output[i])
    {
      Tstack_DAG DAG_set;
      eat_spaces();
      if (redlog_output[i] == ')')
	break;
      assert(redlog_output[i] == '('); /* start of new variable cluster */
      i++;
      eat_spaces();
      assert(redlog_output[i] == '('); /* start new variable list */
      i++;
      eat_spaces();
      stack_INIT(DAG_set);
      while (redlog_output[i] != ')') /* end of variable list */
	{
	  if (!strncmp(redlog_output + i, "v", 9))
	    {
	      TDAG DAG = 0;
	      i += 9;
	      while (redlog_output[i] >= '0' && redlog_output[i] <= '9')
		{
		  DAG *= 10;
		  DAG += redlog_output[i++] - '0';
		}
	      stack_push(DAG_set, DAG);
	    }
	  else
	    jump_end_id();
	  eat_spaces();
	}
      i++;
      eat_spaces();
      /* eat expression */
      while (redlog_output[i] && (redlog_output[i] != ')' || counter))
	{
	  if (redlog_output[i] == '(') counter++;
	  else if (redlog_output[i] == ')')
	    counter--;
	  i++;
	} 
      assert(redlog_output[i] == ')'); /* end of variable cluster */
      i++;
      if (stack_size(DAG_set) >= 2)
	stack_push(partition, DAG_set);
      else
	stack_free(DAG_set);
    }
  for (i = 0; i < stack_size(partition); i++)
    {
      Tstack_DAG DAG_set = stack_get(partition, i);
      TDAG DAGi = stack_get(DAG_set, 0);
      for (j = 1; j < stack_size(DAG_set); j++)
	{
	  TDAG DAGj = stack_get(DAG_set, j);
	  veriT_xenqueue_type(XTYPE_NLA_MODEL_EQ);
	  veriT_xenqueue_DAG(DAGi);
	  veriT_xenqueue_DAG(DAGj);
	}
    }
  for (i = 0; i < stack_size(partition); i++)
    stack_free(stack_get(partition, i));
  stack_free(partition);
  return stack_size(xqueue) != 0;
}

/*--------------------------------------------------------------*/

/*
load_package smtsupp;                                                
on smtsplain;                                                                
smts_mainloop();                                                             
3: (jkdahsdjkash)
error
3: (set-logic QF_NRA)
3: (assert (not (= x X)))
3: (print-assertions)
(not (= x X))
3: (get-model)
error
(((x) x) ((X) X))
3: (check-sat)
sat
3: (get-model)
(((x) infinity1) ((X) X))
3: (assert (= 1 0))
3: (get-model)
error
(((x) x) ((X) X))
3: (check-sat)
unsat
3: (get-model)
error
(((x) x) ((X) X))
3: (reset)
3: (assert (and (= x y) (not (= y z))))
3: (check-sat)
sat
3: (get-model)
(((z) infinity1) ((y x) x))
3: (exit)

4: quit;

Quitting

*/
