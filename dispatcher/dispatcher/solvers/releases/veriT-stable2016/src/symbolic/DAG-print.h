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
  Module for printing formulas and terms
  --------------------------------------------------------------
*/

#ifndef DAG_PRINT_H
#define DAG_PRINT_H

#include <stdio.h>

#include "veriT-DAG.h"

typedef struct TDAG_fprint_opt
{
  bool      newlines;         /**< (true/false) break lines */
  unsigned  columns;          /**< number of columns for printing */
  unsigned  column_to_indent; /**< number of columns of indentation */
  bool      flat;             /**< (true/false) flatten printing
                                 (for terms used multiple times) */
} TDAG_fprint_opt;
extern TDAG_fprint_opt DAG_fprint_opt;

/**
   \author Haniel Barbosa
   \brief prints the syntactic tree, in lisp-notation (for debugging purposes), into string
   \param file the string
   \param DAG the formula to print */
void
DAG_sprint(char * file, TDAG DAG);

/**
   \author Pascal Fontaine
   \brief prints the syntactic tree, in lisp-notation (for debugging purposes)
   \param file the output file
   \param DAG the formula to output */
void DAG_fprint(FILE * file, TDAG DAG);

/**
   \author David Déharbe
   \brief prints the syntactic tree, in lisp-notation (for debugging purposes) on stdout
   \param DAG the formula to output */
void DAG_print(TDAG DAG);

/**
   \brief prints a sort to stdout (useful for debugging)
   \param sort the sort to output */
void DAG_sort_print(Tsort sort);

/**
   \brief prints the syntactic tree, in lisp-notation (for debugging purposes) on stdout, annotated with sort information
   \param DAG the formula to output */
void DAG_print_sort(TDAG DAG);

/**
   \author Pascal Fontaine
   \brief prints the DAG in SMT-LIB 2 notation, without linefeed.  Introduces definitions
   e.g. #12:(+ a 1), so that #12 may later be used
   \param file the output file
   \param DAG the formula to output
   \remark uses the misc field of DAGs.  Take care of side effects with other
   functions that use the same field */
void DAG_fprint_sharing(FILE * file, TDAG DAG);

/**
   \author Pascal Fontaine
   \param DAG the formula to output */
void DAG_fprint_sharing_reset(TDAG DAG);

/**
   \author Pascal Fontaine
   \brief prints formula in Isabelle language (deprecated)
   \param file the output file
   \param DAG the formula to output */
void DAG_isa_fprint(FILE * file, TDAG DAG);

/**
   \author David Deharbe
   \brief prints formula in SMT-LIB 2 notation, as a full benchmark file
   \param file the output file
   \param DAG the formula to output
   \param status the status of the formula */
void DAG_fprint_smt2_bench(FILE * file, TDAG DAG, char * status);

/**
   \author Pascal Fontaine
   \brief prints a set of formulas in SMT-LIB 1 notation, as a full benchmark file
   \param file the output file
   \param PDAG address of an array of DAGs to output
   \param n the number of DAGs to output
   \param status the status of the formula */
void DAG_fprint_smt2_set(FILE * file, TDAG * PDAG, unsigned n, char * status);

void DAG_fprint_smt2_set_gr_DAG(FILE * file, TDAG * DAG, unsigned n, TDAG CI, char * status);

/**
   \author David Deharbe
   \brief prints formula in B notation, as a full machine file
   \param file the output file
   \param DAG the formula to output
   \note only for benchmarks with Bool and Int as sole sorts */
void DAG_fprint_b(FILE * file, TDAG DAG);

/**
   \author Thomas Bouton
   \brief prints a custom error with a printf-like format to stderr.
   Supports all printf-like formats (except $ and %n), and %D for DAGs
   \param format the format string */
void my_DAG_error(char *format, ...);

/**
   \author Thomas Bouton
   \brief prints a custom message with a printf-like format to stderr.
   \remark Supports all printf-like formats (except $ and %n), and %D for DAGs
   \param format the format string */
void my_DAG_message(char *format, ...);

/**
   \author Thomas Bouton
   \brief prints a custom waring with a printf-like format to stderr.
   \remark supports all printf-like formats (except $ and %n), and %D for DAGs
   \param format the format string */
void my_DAG_warning(char *format, ...);
#endif
