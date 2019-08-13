/*
  SMT-lib 2.0 syntax file
  Ver. 2.0 - 20100507
  Pascal Fontaine
*/


%{

#include <stdbool.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#include "general.h"
#include "response.h"

#include "smttypes.h"
#include "smtfun.h"
#include "smtlib2.h"

#define yylineno yy2lineno
#define yyin yy2in
#define yylex_destroy yy2lex_destroy

#define YYMAXDEPTH 1500000

/* PF Uncomment next line to see lots of info about compiler */
/* #define DEBUG_PARSER */

extern int flex(void);
extern int yylineno;

void yyerror(char *s);

void
yyerror(char *s)
{
  if (!strcmp(s,"memory exhausted"))
    printf("The following error may happen on parsing very large"
           " benchmarks.  "
           "If you really want to make the parser read your formula, "
           "you can set \"#define YYMAXDEPTH %d\" in smtsyn.y"
           "to a greater value\n", YYMAXDEPTH);
  my_error("%s on line %d\n", s, yylineno);
}
  /**
     \todo
     there is a cast from Tsort to variables: sort_variable_lookup
  */

%}

%union {
  bool boolean;
  unsigned int numeral;
  char * string;
  T_BIND bind;
  T_BIND_LIST bind_list;
  T_SORT sort;
  T_TERM term;
  T_TERM_LIST term_list;
  T_SORT_LIST sort_list;
  T_VAR var;                 /**< sorted variable */
  T_STACK_VAR stack_var;
  T_NUMERAL_LIST numeral_list;
  T_SYMBOL_LIST symbol_list;
  /* extension of SMT-LIB2 with macros */
  T_MACRO macro;
}

%token	<string>	NUMERAL
%token	<string>	DECIMAL
%token	<string>	HEXADECIMAL
%token	<string>	BINARY
%token	<string>	STRING
%token	<string>	SYMBOL
%token	<string>	KEYWORD

%type	<bind>          bind
%type	<bind_list>	bind_list
%type	<boolean>	b_value
%type	<numeral_list>	numeral_list
%type	<sort>		sort
%type	<sort_list>	sort_list
%type	<sort_list>	sort_list_empty
%type	<var>           var
%type	<stack_var>     stack_var
%type	<stack_var>     stack_var_empty
%type	<string>	spec_const
 /* extension of SMT-LIB2 with generic polymorphism */
%type	<sort>		sort_var
%type	<sort_list>	sort_var_list
%type   <symbol_list>   symbol_list_empty
%type	<term>		term
%type	<term>		term_attr
%type	<term>		lambda
%type	<term_list>	term_list

 /* PF2DD: TODO see if you really want your own token for sort variables
    %token <string> SVAR */
%token TK_EOF

%token TK_BANG "!"
%token TK_UNDERSCORE "_"
%token TK_AS "as"
%token TK_ASSERT "assert"
%token TK_BACKGROUND "background"
%token TK_BOOL "Bool"
%token TK_CHECK_SAT "check-sat"
%token TK_CONTINUED_EXECUTION "continued-execution"
%token TK_DECLARE_FUN "declare-fun"
%token TK_DECLARE_SORT "declare-sort"
%token TK_DEFINE_FUN "define-fun"
%token TK_DEFINE_SORT "define-sort"
%token TK_DISTINCT "distinct"
%token TK_ERROR "error"
%token TK_EXISTS "exists"
%token TK_EXIT "exit"
%token TK_FALSE "false"
%token TK_FORALL "forall"
%token TK_GET_ASSERTIONS "get-assertions"
%token TK_GET_ASSIGNMENT "get-assignment"
%token TK_GET_INFO "get-info"
%token TK_GET_OPTION "get-option"
%token TK_GET_PROOF "get-proof"
%token TK_GET_UNSAT_CORE "get-unsat-core"
%token TK_GET_MODEL "get-model"
%token TK_GET_VALUE "get-value"
%token TK_IMMEDIATE_EXIT "immediate-exit"
%token TK_INCOMPLETE "incomplete"
%token TK_LET "let"
%token TK_LOGIC "logic"
%token TK_NONE "none"
%token TK_NUMERAL "NUMERAL"
%token TK_MEMOUT "memout"
%token TK_PAR "par"
%token TK_POP "pop"
%token TK_PUSH "push"
%token TK_DECIMAL "DECIMAL"
%token TK_SET_INFO "set-info"
%token TK_SET_LOGIC "set-logic"
%token TK_SET_OPTION "set-option"
%token TK_STRING "STRING"
%token TK_THEORY "theory"
%token TK_TRUE "true"
%token TK_UNSUPPORTED "unsupported"

%token TK_PATTERN ":pattern"
%token TK_NAMED ":named"
 /* extension of SMT-LIB2 with lambda expressions */
%token TK_LAMBDA        "@lambda"

/* PF Nb of expected shift/reduce conflict */
/* % e x p e c t 1 */

/* PF when rule file is met, then it is finished */
%start file

%%

file :
/* empty */                   { }
| exit_command                { /* skip */ }
| script                      { /* skip */ }
| script exit_command         { /* skip */ }

script :
command                       { smt2_command(); }
| script command              { smt2_command(); }

command :
  '(' "set-logic" SYMBOL ')'  { smt2_set_logic($3); }
| '(' "set-info" info ')'     { /* PF actual work in subrule */ }
| '(' "set-option" option ')' { /* PF actual work in subrule */ }
| '(' "declare-sort" SYMBOL NUMERAL ')'
                              { smt2_declare_sort($3, $4); }
| '(' "define-sort" SYMBOL '(' symbol_list_empty ')' sort ')'
                              { smt2_define_sort($3, $5, $7); }
| '(' "declare-fun" SYMBOL '(' sort_list_empty ')' sort ')'
                              { smt2_declare_fun($3, $5, $7); }
/* extension of SMT-LIB2 with generic polymorphism */
| '(' "declare-fun" '(' "par" '(' sort_var_list ')'
                     '(' SYMBOL '(' sort_list_empty ')' sort ')' ')' ')'
                              { smt2_declare_poly_fun($9, $6, $11, $13); }
| '(' "define-fun" SYMBOL '(' stack_var_empty ')'
                              { smt2_declare_stack_var($5); }
                                                 sort term ')'
                              { smt2_define_fun($3, $5, $8, $9);
                                smt2_undeclare_stack_var($5); }
| '(' "define-fun" SYMBOL term ')'
                              { smt2_define_fun_short($3, $4); }
/* extension of SMT-LIB2 with generic polymorphism */
| '(' "define-fun" '(' "par" '(' sort_var_list ')'
                              { smt2_declare_sort_var_list($6); }
                    '(' SYMBOL '(' stack_var_empty ')'
                              { smt2_declare_stack_var($12); }
                    sort term ')' ')' ')'
                              { smt2_define_poly_fun($10, /*$6,*/ $12,
                                                     /*$15,*/ $16);
                                smt2_undeclare_stack_var($12);
                                smt2_undeclare_sort_var_list($6); }
| '(' "push" NUMERAL ')'      { smt2_push($3); }
| '(' "pop" NUMERAL ')'       { smt2_pop($3); }
| '(' "assert" term ')'       { smt2_assert($3); }
| '(' "check-sat" ')'         { smt2_check_sat(); }
| '(' "get-assertions" ')'    { smt2_get_assertions(); }
| '(' "get-proof" ')'         { smt2_get_proof(); }
| '(' "get-unsat-core" ')'    { smt2_get_unsat_core(); }
/* PF slight extension over SMT-LIB 2.0: allow empty list */
| '(' "get-value" '(' term_list ')' ')'
                              { smt2_get_value($4); }
| '(' "get-assignment" ')'    { smt2_get_assignment(); }
| '(' "get-info" KEYWORD ')'  { smt2_get_info($3); }
| '(' "get-option" KEYWORD ')'{ smt2_get_option($3); }
| '(' "get-model" ')'         { smt2_get_model(); }

exit_command:
 '(' "exit" ')'               { smt2_exit(); YYACCEPT; }

/* PF
smt2_get_info should react at least to
  :error-behavior
  :name
  :authors
  :version
  :status
  :reason-unknown
  :all-statistics
*/

option :
  KEYWORD                        { smt2_set_option($1); }
| KEYWORD spec_const             { smt2_set_option_num($1, $2); }
| KEYWORD SYMBOL                 { smt2_set_option_str($1, $2); }
| KEYWORD b_value                { smt2_set_option_bool($1, $2); }
| KEYWORD '(' s_expr_list ')'    { /* PF refine if needed */ }
/* PF
smt2_set_option_bool should react at least to:
  :print-success
  :expand-definitions
  :interactive-mode
  :produce-proofs
  :produce-unsat-cores
  :produce-models
  :produce-assignments
smt2_set_option_str should react at least to (with STRING argument):
  :regular-output-channel
  :diagnostic-output-channel
smt2_set_option_str should react at least to (with NUMERAL argument):
  :random-seed
  :verbosity
*/

info :
KEYWORD                       { smt2_set_info($1); }
| KEYWORD spec_const          { smt2_set_info_str($1, $2); }
| KEYWORD SYMBOL              { smt2_set_info_str($1, $2); }
| KEYWORD '(' s_expr_list ')' { /* PF refine if needed */ }

symbol_list_empty :
/* empty */                   { $$ = smt2_symbol_list_new(); }
| symbol_list_empty SYMBOL    { $$ = smt2_symbol_list_add($1, $2); }

/* PF merged rule for identifier, qual_id, term to have access
   to sort and args while looking for symbols */
/* PF we assume this cannot occur as terms
| '(' "as" "true" sort ')'    { $$ = smt2_id_symbol_s("true", $4); }
| '(' "as" "false" sort ')'   { $$ = smt2_id_symbol_s("false", $4); }
| '(' "true" term_list ')'    { $$ = smt2_term_app($2, $3); }
| '(' "false" term_list ')'   { $$ = smt2_term_app($2, $3); }
*/
term :
spec_const                    { $$ = smt2_term_const($1); }
| "true"                      { $$ = smt2_term(strmake("true")); }
| "false"                     { $$ = smt2_term(strmake("false")); }
| SYMBOL                      { $$ = smt2_term($1); }
| '(' '_' SYMBOL numeral_list ')'
                              { $$ = smt2_iterm($3, $4); }
| '(' "as" SYMBOL sort ')'    { $$ = smt2_term_s($3, $4); }
| '(' "as" '(' '_' SYMBOL numeral_list ')' sort ')'
                              { $$ = smt2_iterm_s($5, $6, $8); }
| '(' SYMBOL term_list ')'    { $$ = smt2_term_app($2, $3); }
| '(' '(' '_' SYMBOL numeral_list ')' term_list ')'
                              { $$ = smt2_iterm_app($4, $5, $7); }
| '(' '(' "as" SYMBOL sort ')' term_list ')'
                              { $$ = smt2_term_app_s($4, $7, $5); }
| '(' '(' "as" '(' '_' SYMBOL numeral_list ')' sort ')' term_list ')'
                              { $$ = smt2_iterm_app_s($6, $7, $11, $9); }
| '(' "distinct" term_list ')'
                              { $$ = smt2_term_app("distinct", $3); }
| '(' "let" '(' bind_list ')' { smt2_declare_bind_list($4); }
   term ')'                   { $$ = smt2_let($4, $7);
                                smt2_undeclare_bind_list($4); }
| '(' "forall" '(' stack_var ')' { smt2_declare_stack_var($4); }
   term ')'                   { $$ = smt2_term_forall($4, $7);
                                smt2_undeclare_stack_var($4); }
| '(' "exists" '(' stack_var ')' { smt2_declare_stack_var($4); }
   term ')'                   { $$ = smt2_term_exists($4, $7);
                                smt2_undeclare_stack_var($4); }
| term_attr ')'
                              { $$ = $1; }
/* extension of SMT-LIB2 with lambda expressions */
| lambda                      { $$ = $1; }

/* extension of SMT-LIB2 with lambda expressions */
lambda :
 '(' TK_LAMBDA '(' stack_var ')' { smt2_declare_stack_var($4); }
    term ')'                   { $$ = smt2_term_lambda($4, $7);
                                 smt2_undeclare_stack_var($4); }
| '(' lambda term_list ')'     { $$ = smt2_lambda_app($2, $3); }

term_attr :
  '(' TK_BANG term            { $$ = $3; }
| term_attr KEYWORD           { $$ = smt2_term_attr($1, $2); }
| term_attr KEYWORD attr_value
                              { $$ = smt2_term_attr($1, $2); }
| term_attr TK_NAMED SYMBOL
                              { $$ = smt2_term_attr_named($1, $3); }
| term_attr TK_PATTERN '(' term_list ')'
                              { $$ = smt2_term_attr_pattern($1, $4); }

term_list :
term                          { $$ = smt2_term_list_one($1); }
| term_list term              { $$ = smt2_term_list_add($1, $2); }

bind :
'(' SYMBOL term ')'           { $$ = smt2_bind($2, $3); }

bind_list :
bind                          { $$ = smt2_bind_list_one($1); }
| bind_list bind              { $$ = smt2_bind_list_add($1, $2); }

var :
'(' SYMBOL sort ')'           { $$ = smt2_var($2, $3); }

stack_var :
var                           { $$ = smt2_stack_var_one($1); }
| stack_var var               { $$ = smt2_stack_var_add($1, $2); }

/* extension of SMT-LIB2 with generic polymorphism */
sort_var :
SYMBOL                        { $$ = smt2_sort_var($1); }

sort_var_list :
sort_var                      { $$ = smt2_sort_var_list_one($1); }
| sort_var_list sort_var      { $$ = smt2_sort_var_list_add($1, $2); }

stack_var_empty :
/* empty */                   { $$ = smt2_stack_var_new(); }
| stack_var                   { $$ = $1; }

sort :
"Bool"                        { $$ = smt2_sort_lookup(strmake("Bool")); }
| SYMBOL                      { $$ = smt2_sort_lookup($1); }
| '(' '_' SYMBOL numeral_list ')'
                              { $$ = smt2_sort_lookup_index($3, $4); }
/* PF Parametric sorts like Array of int and list of reals */
| '(' sort sort_list ')'   {
  if (smt2_sort_parametric($2))
    $$ = smt2_sort_apply($2, $3);
  else
    $$ = smt2_sort_functional(list_cons(DAG_ptr_of_sort($2), $3));
  }
/* PF do not authorize such sorts
| "true"                      { $$ = smt2_sort_id(strmake("true")); }
| "false"                     { $$ = smt2_sort_id(strmake("false")); }
*/

sort_list :
sort                          { $$ = smt2_sort_list_one($1); }
| sort_list sort              { $$ = smt2_sort_list_add($1, $2); }

sort_list_empty :
/* empty */                   { $$ = smt2_sort_list_new(); }
| sort_list                   { $$ = $1; }

numeral_list :
NUMERAL                       { $$ = smt2_numeral_list_one($1); }
| numeral_list NUMERAL        { $$ = smt2_numeral_list_add($1, $2); }


/*
  DD: I wrote the grammar assuming that there is a type in the last rule of p.71
  The grammar implements
  <attribute> ::= <keyword> | <keyword> <attribute_value>
  instead of
  <attribute> ::= <keyword> | <keyword> <s_expr>
*/

attr_value :                /* DD this is for s_expr in an attribute list */
spec_const                    { /* PF TODO abstract */ }
| SYMBOL                      { /* PF TODO abstract */ }
| '(' s_expr_list ')'         { /* PF TODO abstract */ }

s_expr :
spec_const                    { /* PF TODO abstract */ }
| SYMBOL                      { /* PF TODO abstract */ }
| KEYWORD                     { /* PF TODO abstract */ }
| '(' s_expr_list ')'         { /* PF TODO abstract */ }

s_expr_list :
/* empty */                   { /* PF TODO abstract */ }
| s_expr_list s_expr          { /* PF TODO abstract */ }

spec_const :
NUMERAL                       { $$ = $1; }
| DECIMAL                     { $$ = $1; }
| HEXADECIMAL                 { $$ = $1; }
| BINARY                      { $$ = $1; }
| STRING                      { $$ = $1; }

b_value :
"true"                        { $$ = true; }
| "false"                     { $$ = false; }


%%

extern void initlex(char *arg);

extern FILE *yyin;

void
parse_smtlib2(FILE * input, bool option_disable_print_success)
{
#ifdef DEBUG_PARSER
  yydebug = 1;
#endif
  yylineno = 1;
  yyin = input;
  if (!yyin)
    veriT_error("parse_smtlib2: no input file");
  smt2_init(option_disable_print_success);
  yyparse();
  smt2_done();
  yylex_destroy();
}
