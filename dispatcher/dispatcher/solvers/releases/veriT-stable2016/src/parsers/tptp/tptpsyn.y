/*
  TPTP syntax file
  Ver. 1.0 - 20131202
  Federico Dobal
*/


%{

#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#include "general.h"
#include "response.h"

#include "smttypes.h"
#include "smtfun.h"
#include "tptp.h"
#include "tptp_fun.h"

#define yylineno yy3lineno
#define yyin yy3in
#define yylex_destroy yy3lex_destroy
#define yyinitfile yy3initfile

#define YYMAXDEPTH 1500000

/*--------------------------------------------------------------*/

/* FD stack to accumulate variables from CNF formulas for later universal quantification */
T_STACK_VAR stack_var;

/*--------------------------------------------------------------*/

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
           "you can set \"#define YYMAXDEPTH %d\" in tptpsyn.y"
           "to a greater value\n", YYMAXDEPTH);
  my_error("%s on line %d\n", s, yylineno);
}

%}

/*--------------------------------------------------------------*/

%union {
  char * string;
  T_BIND bind;
  T_BIND_LIST bind_list;
  T_SORT sort;
  T_TERM term;
  T_TERM_LIST term_list;
  T_SORT_LIST sort_list;
  T_VAR var;            
  T_STACK_VAR stack_var;
  T_NUMERAL_LIST numeral_list;
  T_SYMBOL_LIST symbol_list;
  T_MACRO macro;
}

/*--------------------------------------------------------------*/

/* FD exports token table for lex */

%token TK_EOF
%token TK_TPI                 "tpi"
%token TK_THF                 "thf"
%token TK_TFF                 "tff"
%token TK_FOF                 "fof"    
%token TK_CNF                 "cnf"   
%token TK_ITE_F               "$ite_f"
%token TK_LET_TF              "$let_tf"
%token TK_LET_FF              "$let_ff"
%token TK_ITE_T               "$ite_t"
%token TK_LET_FT              "$let_ft"
%token TK_LET_TT              "$let_tt"
%token TK_EXCLAMATION_ARROW   "!>"
%token TK_QUESTION_STAR       "?*"
%token TK_PLUS_ARROBA         "@+"
%token TK_MINUS_ARROBA        "@-"
%token TK_DOUBLE_EXCLAMATION  "!!"
%token TK_DOUBLE_QUESTION     "??"
%token TK_IFF                 "<=>"
%token TK_RIGHT_IMP           "=>"
%token TK_LEFT_IMP            "<="
%token TK_EQUIV               "<~>"
%token TK_NEG_AMPERSAND       "~&"
%token TK_GENTZEN_ARROW       "-->"
%token TK_INFIX_INEQUALITY    "!="
%token TK_SUBTYPE_SIGN        "<<"

/*--------------------------------------------------------------*/

%token	<string>	DO_ESCAPE
%token	<string>	SQ_ESCAPE
%token	<string>	SP_CHAR
%token	<string>	DISTINCT_OBJECT
%token	<string>	SINGLE_QUOTED
%token	<string>	DOLLAR_WORD
%token	<string>	DOLLAR_DOLLAR_WORD
%token	<string>	VARIABLE
%token	<string>	LOWER_WORD
%token	<string>	REAL
%token	<string>	RATIONAL
%token	<string>	INTEGER

/*--------------------------------------------------------------*/

%token	<string>	TK_COMMENT_BLOCK
%token	<string>	TK_COMMENT_LINE

/*--------------------------------------------------------------*/
%type   <term>          tff_formula
%type   <term>          fof_formula
%type   <term>          cnf_formula
%type   <term>          disjunction
%type   <term>          literal
%type   <term>          atomic_formula
%type   <term>          plain_atomic_formula
%type   <term>          plain_term
%type   <term>          plain_term_prop
%type   <term>          defined_plain_term_prop
%type   <term_list>     arguments
%type   <string>        atomic_word
%type   <term>          term
%type   <term>          defined_atomic_formula
%type   <term>          defined_plain_formula
%type   <term>          defined_plain_term
%type   <string>        atomic_defined_word
%type   <term>          defined_infix_formula
%type   <term>          system_atomic_formula
%type   <term>          system_term
%type   <term>          defined_term
%type   <term>          fof_unitary_formula
%type   <term>          fof_logic_formula
%type   <term>          fof_binary_formula
%type   <term>          fof_or_formula
%type   <term>          fof_and_formula
%type   <term>          fof_unary_formula
%type   <term>          fol_infix_unary
%type   <stack_var>     fof_variable_list
%type   <term>          fof_tuple_left
%type   <term>          fof_tuple_right
%type   <term>          tff_tuple_left
%type   <term>          tff_tuple_right
%type   <string>        defined_type
%type   <string>        name
%type   <term>          number
%type   <string>        formula_role
%type   <term>          tff_logic_formula
%type   <term>          tff_binary_formula
%type   <term>          tff_or_formula
%type   <term>          tff_and_formula
%type   <term>          tff_unitary_formula
%type   <stack_var>     tff_variable_list
%type   <var>           tff_variable
%type   <term>          tff_unary_formula
%type   <term>          tff_let_term_binding
%type   <string>        tff_let_formula_defn
%type   <string>        tff_let_formula_binding
%type   <term>          tff_sequent
%type   <term_list>     tff_tuple_list
%type   <term>          tff_typed_atom
%type   <string>        tff_untyped_atom
%type   <sort_list>     tff_unitary_type
%type   <sort_list>     tff_type_arguments
%type   <sort_list>     tff_xprod_type
%type   <string>        fol_quantifier
%type   <string>        binary_connective
%type   <term>          conditional_term
%type   <term>          let_term
%type   <sort>          tff_atomic_type
%type   <term>          fof_sequent
%type   <term_list>     fof_tuple_list
%type   <string>        atomic_system_word

/*--------------------------------------------------------------*/

%start tptp_file

%%

tptp_file :
/* empty */                   { } 
| tptp_file annotated_formula { }

 /* Formula records */
annotated_formula :
  "tff" '(' name ',' formula_role ',' tff_formula annotations ')' '.'
                              { 
                                tptp_define_formula_role($7, $5, yy3lineno); 
                                set_is_tff(1);
                                free($3);
                              }
| "fof" '(' name ',' formula_role ',' fof_formula annotations ')' '.'
                              { 
                                tptp_define_formula_role($7, $5, yy3lineno); 
                                free($3);
                              }
| "cnf" '(' name ',' formula_role ',' cnf_formula annotations ')' '.'
                              { 
                                tptp_define_formula_role($7, $5, yy3lineno); 
                                free($3); 
                              }
| "tpi" '(' name ',' formula_role ',' fof_formula annotations ')' '.'   
                              { 
                                tptp_define_formula_role($7, $5, yy3lineno); 
                                free($3); 
                              }
| TK_COMMENT_LINE             { 
                                if (strncmp($1, "% Status   :", strlen("% Status   :")) == 0)
                                  tptp_set_formula_status($1);
                                free($1);
                              }
| TK_COMMENT_BLOCK            { }

annotations :
/* empty */                   { }
| ',' source optional_info    { }

/* FD Types for problems. */
formula_role :
  LOWER_WORD                  { $$ = $1; }

/* FD TFF formulae. */
tff_formula :
  tff_logic_formula           { $$ = $1; }
| tff_typed_atom              { $$ = $1; }
| tff_sequent                 { $$ = $1; }

tff_logic_formula :
  tff_binary_formula          { $$ = $1; }
| tff_unitary_formula         { $$ = $1; }

tff_binary_formula :
  tff_unitary_formula binary_connective tff_unitary_formula 
                              { $$ = tptp_define_binary_formula($1, $3, $2); }
| tff_or_formula              { $$ = $1; }
| tff_and_formula             { $$ = $1; }

tff_or_formula :
  tff_unitary_formula '|' tff_unitary_formula 
                              { $$ = tptp_binary_term($1, $3, strmake("or")); }
| tff_or_formula '|' tff_unitary_formula 
                              { $$ = tptp_binary_term($1, $3, strmake("or")); }

tff_and_formula : 
  tff_unitary_formula '&' tff_unitary_formula 
                              { $$ = tptp_binary_term($1, $3, strmake("and")); }
| tff_and_formula '&' tff_unitary_formula 
                              { $$ = tptp_binary_term($1, $3, strmake("and")); }

tff_unitary_formula : 
  fol_quantifier '[' tff_variable_list ']' 
                              { smt2_declare_stack_var($3); }
                    ':' tff_unitary_formula 
                              { 
                                $$ = smt2_term_forall($3, $7);
                                smt2_undeclare_stack_var($3);
                              }
| tff_unary_formula           { $$ = $1; }
| atomic_formula              { $$ = $1; }
| "$ite_f" '(' tff_logic_formula ',' tff_logic_formula ',' tff_logic_formula ')'       
                              { 
                                 T_TERM_LIST term_list = smt2_term_list_one($3);
                                 term_list = smt2_term_list_add(term_list, $5);
                                 term_list = smt2_term_list_add(term_list, $7);
                                 $$ = smt2_term_app(strmake("ite"), term_list);
                              }
| "$let_tf" '(' tff_let_term_defn ',' tff_formula ')' 
                              { tptp_error_not_implemented("let_tf", yy3lineno); }
| "$let_ff" '(' tff_let_formula_defn ',' tff_formula ')' 
                              { tptp_error_not_implemented("let_ff", yy3lineno); }
| '(' tff_logic_formula ')'   { $$ = $2; }

tff_variable_list :
  tff_variable                { $$ = smt2_stack_var_one($1); }
| tff_variable ',' tff_variable_list              
                              { $$ = smt2_stack_var_add($3, $1); }

tff_variable :
  VARIABLE ':' tff_atomic_type                     
                              { $$ = smt2_var($1, $3); }
| VARIABLE                    { 
                                $$ = smt2_var($1, smt2_sort_lookup(strmake("U")));
                              }

tff_unary_formula :
  '~' tff_unitary_formula     { 
                                $$ = smt2_term_app(strmake("not"), smt2_term_list_one($2));
                              }
| fol_infix_unary             { $$ = $1; }

tff_let_term_defn :
  '!' '['  tff_variable_list ']' ':' tff_let_term_defn 
                              { tptp_error_not_implemented("tff_let_term_defn", yy3lineno); }
| tff_let_term_binding        { tptp_error_not_implemented("tff_let_term_defn", yy3lineno); }

tff_let_term_binding :
  term '=' term               { tptp_error_not_implemented("tff_let_term_binding", yy3lineno); }
| '(' tff_let_term_binding ')'
                              { tptp_error_not_implemented("tff_let_term_binding", yy3lineno); }

tff_let_formula_defn :
  '!' '[' tff_variable_list ']' ':' tff_let_formula_defn
                              { tptp_error_not_implemented("tff_let_formula_defn", yy3lineno); }
| tff_let_formula_binding     { tptp_error_not_implemented("tff_let_formula_defn", yy3lineno); }

tff_let_formula_binding :
  atomic_formula "<=>" tff_unitary_formula 
                              { tptp_error_not_implemented("tff_let_formula_binding", yy3lineno); }
| '(' tff_let_formula_binding ')' 
                              { tptp_error_not_implemented("tff_let_formula_binding", yy3lineno); }

tff_sequent :
  /* FD Gentzen arrow */
  tff_tuple_left "-->" tff_tuple_right 
                              { $$ = tptp_binary_term($1, $3, strmake("=>")); }
| '(' tff_sequent ')'         { $$ = $2; }

tff_tuple_left :
  '[' ']'                     { $$ = smt2_term(strmake("true")); }
| '[' tff_tuple_list ']'      { $$ = smt2_term_app(strmake("and"), $2); }

tff_tuple_right:
  '[' ']'                     { $$ = smt2_term(strmake("false")); }
| '[' tff_tuple_list ']'      { $$ = smt2_term_app(strmake("or"), $2); }

tff_tuple_list :
  tff_logic_formula           { $$ = smt2_term_list_one($1); }
| tff_logic_formula ',' tff_tuple_list            
                              { $$ = smt2_term_list_add($3, $1); }

tff_typed_atom :
/* FD tff_untyped_atom ':' tff_top_level_type */
/* FD Semantic: define a sort name */
  tff_untyped_atom ':' tff_atomic_type 
                              { smt2_declare_fun($1, NULL, $3); }  
| tff_untyped_atom ':' tff_unitary_type '>' tff_atomic_type 
                              { smt2_declare_fun(tptp_conv_reserved_word($1), $3, $5); }
/* FD |tff_untyped_atom ':' TK_EXCLAMATION_ARROW '[' tff_variable_list ']' ':' tff_monotype */
| tff_untyped_atom ':' "!>" '[' tff_variable_list ']' ':' tff_atomic_type
                              { tptp_error_not_implemented("tff_quantified_type", yy3lineno); } 
| tff_untyped_atom ':' "!>" '[' tff_variable_list ']' ':' 
                    '(' tff_unitary_type '>' tff_atomic_type ')'
                              { tptp_error_not_implemented("tff_quantified_type", yy3lineno); } 
| tff_untyped_atom ':' '(' tff_atomic_type ')'
                              { smt2_define_sort($1, smt2_symbol_list_new(), $4); }
| tff_untyped_atom ':' '(' tff_unitary_type '>' tff_atomic_type ')'
                              { smt2_declare_fun(strmake($1), $4, $6); }
/* FD |tff_untyped_atom ':' '(' TK_EXCLAMATION_ARROW '[' tff_variable_list ']' ':' tff_monotype ')' */
| tff_untyped_atom ':' '(' "!>" '[' tff_variable_list ']' ':' tff_atomic_type ')'
                              { tptp_error_not_implemented("tff_quantified_type", yy3lineno); }
| tff_untyped_atom ':' '(' "!>" '[' tff_variable_list ']' ':' 
                    '(' tff_unitary_type '>' tff_atomic_type ')' ')'
                              { tptp_error_not_implemented("tff_quantified_type", yy3lineno); }
| '(' tff_typed_atom ')'      { $$ = $2; }

tff_untyped_atom : 
  atomic_word                 { $$ = $1; }
| atomic_system_word          { $$ = $1; }

tff_unitary_type :
  tff_atomic_type             { $$ = smt2_sort_list_one($1); }
| '(' tff_xprod_type ')'      { $$ = $2; }

tff_atomic_type :
  atomic_word                 { $$ = smt2_sort_lookup(strmake($1)); }
| defined_type                { 
                                char * sort_name = NULL;
                                if (!strcmp($1, "$int"))
                                  sort_name = strmake("Int");
                                if (!strcmp($1, "$real"))
                                  sort_name = strmake("Real");
                                if (!strcmp($1, "$rat"))
                                  tptp_error_not_implemented("$rat", yy3lineno);
                                if (!strcmp($1, "$o") || !strcmp($1, "$oType"))
                                  sort_name = strmake("Bool");
                                if (!strcmp($1, "$tType"))
                                  tptp_error_not_implemented("$tType", yy3lineno);
                                if (!strcmp($1, "$i") || !strcmp($1, "$iType"))
                                  {
                                    my_warning("$iType compiled to SMT2-LIB as (declare-sort U 0).\n");
                                    sort_name = strmake("U");
                                  }
                                if (sort_name == NULL)
                                  veriT_error("parse_tptp: defined_type not recognized");
                                else
                                 $$ = smt2_sort_lookup(sort_name);
                                free($1);
                              }
| atomic_word '(' tff_type_arguments ')' 
                              { 
                                smt2_declare_sort(strmake($1), strmake("0"));
                                $$ = smt2_sort_lookup(strmake($1));
                              }
| VARIABLE 
                              { 
                                smt2_declare_sort(strmake($1), strmake("0"));
                                $$ = smt2_sort_lookup(strmake($1));
                              }

tff_type_arguments :
  tff_atomic_type             { $$ = smt2_sort_list_one($1); }
| tff_atomic_type ',' tff_type_arguments 
                              { $$ = smt2_sort_list_add($3, $1); }

tff_xprod_type :
  tff_unitary_type '*' tff_atomic_type 
                              { $$ = smt2_sort_list_add($1, $3); }
| tff_xprod_type '*' tff_atomic_type 
                              { $$ = smt2_sort_list_add($1, $3); }

/* FOF formulae. */
fof_formula :
  fof_logic_formula           { $$ = $1; }
| fof_sequent                 { $$ = $1; }

fof_logic_formula :
  fof_binary_formula          { $$ = $1; }
| fof_unitary_formula         { $$ = $1; }

fof_binary_formula :
  fof_unitary_formula binary_connective fof_unitary_formula 
                              { $$ = tptp_define_binary_formula($1, $3, $2); }
| fof_or_formula              { $$ = $1; }
| fof_and_formula             { $$ = $1; }

fof_or_formula :
  fof_unitary_formula '|' fof_unitary_formula 
                              { $$ = tptp_binary_term($1, $3, strmake("or")); }
| fof_or_formula '|' fof_unitary_formula 
                              { $$ = tptp_binary_term($1, $3, strmake("or")); }

fof_and_formula :
  fof_unitary_formula '&' fof_unitary_formula
                              { $$ = tptp_binary_term($1, $3, strmake("and")); }
| fof_and_formula '&' fof_unitary_formula
                              { $$ = tptp_binary_term($1, $3, strmake("and")); }

fof_unitary_formula :
  fol_quantifier '[' fof_variable_list ']' { smt2_declare_stack_var($3); } ':' fof_unitary_formula 
                              { 
                                if(!(strcmp($1,"!")))
                                  $$ = smt2_term_forall($3, $7);
                                else if(! (strcmp($1,"?")))
                                  $$ = smt2_term_exists($3, $7);
                                else
                                  veriT_error("parse_tptp: fol_quantifier unknown");
                                smt2_undeclare_stack_var($3);
                              }
| fof_unary_formula           { $$ = $1; }
| atomic_formula              { $$ = $1; }
| '(' fof_logic_formula ')'   { $$ = $2; }

fof_variable_list :
 VARIABLE  
                              { 
                                T_SORT sort_ptr = smt2_sort_lookup(strmake("U"));
                                T_VAR var = smt2_var($1, sort_ptr);
                                $$ = smt2_stack_var_one(var);
                              }
| VARIABLE ',' fof_variable_list 
                              { 
                                T_SORT sort_ptr = smt2_sort_lookup(strmake("U"));
                                T_VAR var = smt2_var($1, sort_ptr);
                                $$ = smt2_stack_var_add($3, var);
                              }

fof_unary_formula : 
  '~' fof_unitary_formula     { 
                                T_TERM_LIST term_list = smt2_term_list_one($2);
                                $$ = smt2_term_app(strmake("not"), term_list);
                              }
| fol_infix_unary             { $$ = $1; }

fof_sequent :
  /* FD Gentzen arrow */
  fof_tuple_left "-->" fof_tuple_right 
                              { $$ = tptp_binary_term($1, $3, strmake("=>")); }
| '(' fof_sequent ')'         { $$ = $2; }

/* FD fof_tuple
'[' ']'
|'[' fof_tuple_list ']' */
fof_tuple_left :
  '[' ']'                     { $$ = smt2_term(strmake("true")); }
| '[' fof_tuple_list ']'      { $$ = smt2_term_app(strmake("and"), $2); }

fof_tuple_right :
  '[' ']'                     { $$ = smt2_term(strmake("false"));; }
| '[' fof_tuple_list ']'      { $$ = smt2_term_app(strmake("or"), $2); }

fof_tuple_list :
  fof_logic_formula           { $$ = smt2_term_list_one($1); }
| fof_logic_formula ',' fof_tuple_list            
                              { $$ = smt2_term_list_add($3, $1); }

/* FD CNF formulae (variables implicitly universally quantified) */
cnf_formula :
  '(' disjunction ')'     
                              { 
                                if (stack_size(stack_var) == 0)
                                  $$ = $2;
                                else
                                  {
                                    $$ = smt2_term_forall(stack_var, $2);
                                    free(stack_var);
                                    stack_var = smt2_stack_var_new();
                                  }
                              }
| disjunction                 {                    
                                if (stack_size(stack_var) == 0)
                                  $$ = $1;
                                else
                                  {
                                    $$ = smt2_term_forall(stack_var, $1);
                                    free(stack_var);
                                    stack_var = smt2_stack_var_new();
                                  }
                              }

disjunction :
  literal                     { $$ = $1; }
| disjunction '|' literal     
                              { $$ = tptp_binary_term($1, $3, strmake("or")); }

literal :
  atomic_formula              { $$ = $1; }
| '~' atomic_formula    
                              { 
                                T_TERM_LIST term_list = smt2_term_list_one($2);
                                $$ = smt2_term_app(strmake("not"), term_list);
                              }
| fol_infix_unary             { $$ = $1; }

fol_infix_unary :
/* FD expand left hand side term in order to disambiguate the TPTP grammar
      in order to avoid YACC confict messages.
      Instead of using the rule
        term TK_INFIX_INEQUALITY term
      we use the rule
        plain_term   TK_INFIX_INEQUALITY term
        defined_term TK_INFIX_INEQUALITY term
        system_term  TK_INFIX_INEQUALITY term
*/
/* FD plain_term */
  atomic_word "!=" term 
                              { 
                                T_SORT sort_ptr = smt2_sort_lookup(strmake("U"));
                                T_TERM term_eq = tptp_define_term_app_const(strmake("="), $1, sort_ptr, $3);
                                /* FD Negation */
                                T_TERM_LIST term_list = smt2_term_list_one(term_eq);
                                $$ = smt2_term_app(strmake("not"), term_list);
                                free($1);
                              }
| atomic_word '(' arguments ')' "!=" term 
                              { 
                                T_SORT sort_ptr = smt2_sort_lookup(strmake("U"));
                                T_TERM term_eq = tptp_define_term_app_fun(strmake("="), $1, sort_ptr, $3, $6);
                                /* FD Negation */
                                T_TERM_LIST term_list = smt2_term_list_one(term_eq);
                                $$ = smt2_term_app(strmake("not"), term_list);
                                free($1);
                              }
/* FD defined_term */
| number "!=" term 
                              { 
                                T_TERM term_eq = tptp_binary_term($1, $3, strmake("="));
                                T_TERM_LIST term_list = smt2_term_list_one(term_eq);
                                /* FD Negation */
                                $$ = smt2_term_app(strmake("not"), term_list);
                              }
| DISTINCT_OBJECT "!=" term 
                              { 
                                T_TERM term_dist = smt2_term_const($1);
                                T_TERM term_eq = tptp_binary_term(term_dist, $3, strmake("="));
                                T_TERM_LIST term_list = smt2_term_list_one(term_eq);
                                /* FD Negation */
                                $$ = smt2_term_app(strmake("not"), term_list);
                              }
| atomic_defined_word "!=" term 
                              { 
                                T_SORT sort_ptr = smt2_sort_lookup(strmake("U"));
                                T_TERM term_eq = tptp_define_term_app_const(strmake("="), $1, sort_ptr, $3);
                                /* FD Negation */
                                T_TERM_LIST term_list = smt2_term_list_one(term_eq);
                                $$ = smt2_term_app(strmake("not"), term_list);
                              }
| atomic_defined_word '(' arguments ')' "!=" term 
                              { 
                                T_TERM term_1, term_eq;
                                T_TERM_LIST term_list;
                                char *smt_symb;
                                tptp_to_smt($1, yy3lineno, &smt_symb);
                                term_1 = smt2_term_app(smt_symb, $3);
                                term_eq = tptp_binary_term(term_1, $6, strmake("="));
                                /* FD Negation */
                                term_list = smt2_term_list_one(term_eq);
                                $$ = smt2_term_app(strmake("not"), term_list);
                                free($1);
                              }
/* FD system_term */
| atomic_system_word "!=" term 
                              { 
                                T_SORT sort_ptr = smt2_sort_lookup(strmake("U"));
                                T_TERM term_eq = tptp_define_term_app_const(strmake("="), $1, sort_ptr, $3);
                                /* FD Negation */
                                T_TERM_LIST term_list = smt2_term_list_one(term_eq);
                                $$ = smt2_term_app(strmake("not"), term_list);
                              }
| atomic_system_word '(' arguments ')' "!=" term 
                              { 
                                T_SORT sort_ptr = smt2_sort_lookup(strmake("U"));
                                T_TERM term_eq = tptp_define_term_app_fun(strmake("="), $1, sort_ptr, $3, $6);
                                /* FD Negation */
                                T_TERM_LIST term_list = smt2_term_list_one(term_eq);
                                $$ = smt2_term_app(strmake("not"), term_list);
                              }
| VARIABLE "!=" term 
                              { 
                                T_VAR var;
                                T_SORT sort_ptr;
                                T_TERM term_1, term_eq;
                                T_TERM_LIST term_list_neg;
                                /* sort_ptr = smt2_sort_lookup(strmake("U")); */
                                sort_ptr = DAG_sort($3);
                                var = smt2_var(strmake($1), sort_ptr);
                                stack_var = smt2_stack_var_add(stack_var, var);
                                term_1 = smt2_term(strmake($1));  
                                term_eq = tptp_binary_term(term_1, $3, strmake("="));
                                /* FD Negation */
                                term_list_neg = smt2_term_list_one(term_eq);
                                $$ = smt2_term_app(strmake("not"), term_list_neg);
                                free($1);
                              }
| conditional_term "!=" term 
                              { 
                                T_TERM_LIST term_list_neg;
                                T_TERM term_eq = tptp_binary_term($1, $3, strmake("="));
                                /* FD Negation */
                                term_list_neg = smt2_term_list_one(term_eq);
                                $$ = smt2_term_app(strmake("not"), term_list_neg);
                              }
| let_term "!=" term 
                              {  
                                T_TERM_LIST term_list_neg;
                                T_TERM term_eq = tptp_binary_term($1, $3, strmake("=")); 
                                /* FD Negation */
                                term_list_neg = smt2_term_list_one(term_eq);
                                $$ = smt2_term_app(strmake("not"), term_list_neg);
                              }

/* FD Connectives */

fol_quantifier :
  '!'                         { $$ = "!"; }
| '?'                         { $$ = "?"; }

/* FD these binary connectives do not include neither & nor | because the TPTP grammar
      take apart then due to its associativity property */
binary_connective :
  "<=>"                       { $$ = "iff"; }
| "=>"                        { $$ = "=>"; }
| "<="                        { $$ = "<="; }
| "<~>"                       { $$ = "<~>"; }
| '~' '|'                     { $$ = "~|"; }
| "~&"                        { $$ = "~&"; }


/* FD Types for THF and TFF */
defined_type :
  atomic_defined_word         { 
                                tptp_check_defined_type($1, yy3lineno);
                                $$ = $1;
                              }

/* FD first order atoms */
atomic_formula : 
  plain_atomic_formula        { $$ = $1; }
| defined_atomic_formula      { $$ = $1; }
| system_atomic_formula       { $$ = $1; }

plain_atomic_formula :
  plain_term_prop             { $$ = $1; }

defined_atomic_formula :
  defined_plain_formula       { $$ = $1; }
| defined_infix_formula       { $$ = $1; }

defined_plain_formula :
  defined_plain_term_prop     { $$ = $1; }

/* FD grammar modifications */
defined_infix_formula :
/* FD expand left hand side term in order to disambiguate the TPTP grammar
      avoiding YACC confict messages.
      Instead of using the rule
        term TK_INFIX_INEQUALITY term
      whe use the rule
        plain_term   TK_INFIX_INEQUALITY term
        defined_term TK_INFIX_INEQUALITY term
        system_term  TK_INFIX_INEQUALITY term
*/
/* FD plain_term */
  atomic_word '=' term 
                              {
                                T_SORT sort_ptr;
                                if (smt2_sort_lookup(strmake("U")) != DAG_sort($3)) {
                                  free_axiom_path();
                                  tptp_error("constant [%s] and term [%s] do not have the same type in line [%d]", $1,
                                             DAG_symb_name2(DAG_symb($3)), yy3lineno);
                                }
                                sort_ptr = smt2_sort_lookup(strmake("U"));
                                $$ = tptp_define_term_app_const(strmake("="), $1, sort_ptr, $3);
                                free($1);
                              }
| atomic_word '(' arguments ')' '=' term 
                              { 
                                Tlist list_sorts;
                                unsigned i;
                                T_TERM term_1;
                                char * name_app;
                                T_SORT sort_ptr;
                                if (smt2_sort_lookup(strmake("U")) != DAG_sort($6)) {
                                  free_axiom_path();
                                  tptp_error("function application [%s] and term  [%s] do not have the same type in line [%d]", $1,
                                             DAG_symb_name2(DAG_symb($6)), yy3lineno);
                                }                             
                                sort_ptr = (T_SORT)(intptr_t) DAG_sort($6);
                                name_app = tptp_conv_reserved_word($1);
                                list_sorts = smt2_sort_list_new();
                                for (i = 0; i < list_length($3); i++) {
                                  T_TERM t = (T_TERM)(intptr_t) list_n($3, (int)i);
                                  T_SORT sort = (T_SORT)(intptr_t) DAG_sort(t);
                                  list_sorts = smt2_sort_list_add(list_sorts, sort);
                                }
                                if (!get_is_tff())
                                  smt2_declare_fun(name_app, list_sorts, sort_ptr);
                                term_1 = smt2_term_app(name_app, $3);
                                $$ = tptp_binary_term(term_1, $6, strmake("=")); 
                              }
/* FD defined_term */
| number '=' term 
                              { 
                                T_TERM_LIST term_list = smt2_term_list_one($1);
                                term_list = smt2_term_list_add(term_list, $3);
                                $$ = smt2_term_app(strmake("="), term_list);
                              }
| DISTINCT_OBJECT '=' term 
                              { 
                                T_TERM term_dist = smt2_term_const($1);
                                $$ = tptp_binary_term(term_dist, $3, strmake("="));
                                
                              }
| atomic_defined_word '=' term 
                              { 
                                T_SORT sort_ptr = smt2_sort_lookup(strmake("U"));
                                $$ = tptp_define_term_app_const(strmake("="), $1, sort_ptr, $3);
                              }
| atomic_defined_word '(' arguments ')' '=' term 
                              { 
                                char * def_func;
                                tptp_check_defined_functor($1, yy3lineno);
                                tptp_to_smt($1, yy3lineno, &def_func);
                                if (def_func == NULL)
                                  veriT_error("parse_tptp: defined_type not recognized on line %d", yy3lineno);
                                else
                                  {
                                    /* FD Apply the function name change */
                                    T_TERM term_1 = smt2_term_app(def_func, $3);
                                    /* FD Create the binary term applying = */
                                    $$ = tptp_binary_term(term_1, $6, strmake("=")); 
                                  }
                                free($1);
                              }
/* FD system_term */
| atomic_system_word '=' term 
                              { 
                                T_SORT sort_ptr = smt2_sort_lookup(strmake("U"));
                                $$ = tptp_define_term_app_const(strmake("="), $1, sort_ptr, $3);
                              }
| atomic_system_word '(' arguments ')'  '=' term 
                              { 
                                T_SORT sort_ptr = smt2_sort_lookup(strmake("U"));
                                $$ = tptp_define_term_app_fun(strmake("="), $1, sort_ptr, $3, $6);
                              }
| VARIABLE '=' term 
                              { 
                                T_VAR var;
                                T_TERM term_1;
                                T_SORT sort_ptr = (T_SORT)(intptr_t) DAG_sort($3);
                                var = smt2_var(strmake($1), sort_ptr);
                                stack_var = smt2_stack_var_add(stack_var, var);
                                term_1 = smt2_term(strmake($1)); 
                                $$ = tptp_binary_term(term_1, $3, strmake("=")); 
                                free($1);
                              }
| conditional_term '=' term  
                              { $$ = tptp_binary_term($1, $3, strmake("=")); }
| let_term '=' term                 
                              { $$ = tptp_binary_term($1, $3, strmake("=")); }

system_atomic_formula :
  system_term                 { $$ = $1; }

/* First order terms */
term :
  plain_term                  { $$ = $1; }
| defined_term                { $$ = $1; }
| system_term                 { $$ = $1; }
| VARIABLE                    { 
                                T_SORT sort_ptr = smt2_sort_lookup(strmake("U"));
                                T_VAR var = smt2_var(strmake($1), sort_ptr);
                                stack_var = smt2_stack_var_add(stack_var, var);
                                $$ = smt2_term(strmake($1)); 
                                free($1);                   
                              }
| conditional_term            { $$ = $1; }
| let_term                    { $$ = $1; }

plain_term :
  atomic_word                 { 
                                T_SORT sort_ptr = smt2_sort_lookup(strmake("U"));
                                char *name_app = tptp_conv_reserved_word($1);
                                if (!get_is_tff())
                                  smt2_declare_fun(name_app, NULL, sort_ptr);
                                $$ = smt2_term(name_app);
                              }
| atomic_word '(' arguments ')' 
                              { $$ = tptp_define_term_fun($1, $3, smt2_sort_lookup(strmake("U"))); }

/* FD plain_atomic_formula (propositional modification)*/
plain_term_prop :
 atomic_word                  { 
                                T_SORT sort_ptr = smt2_sort_lookup(strmake("Bool"));
                                if (!get_is_tff())
                                  smt2_declare_fun(strmake($1), NULL, sort_ptr);
                                $$ = smt2_term($1); 
                              }
| atomic_word '(' arguments ')' 
                              { 
                                T_SORT sort_ptr;
                                unsigned i;
                                char *name_app = tptp_conv_reserved_word($1);
                                if (!get_is_tff()){
                                  Tlist list_sorts = smt2_sort_list_new();
                                  for (i = 0; i < list_length($3); i++) {
                                    T_TERM t = (T_TERM)(intptr_t) list_n($3, (int)i);
                                    T_SORT sort = (T_SORT)(intptr_t) DAG_sort(t);
                                    list_sorts = smt2_sort_list_add(list_sorts, sort);
                                  }
                                  sort_ptr = smt2_sort_lookup(strmake("Bool"));
                                  smt2_declare_fun(name_app, list_sorts, sort_ptr);
                                }
                                $$ = smt2_term_app(name_app, $3);
                              }

defined_term :
  number                      { $$ = $1; }
| DISTINCT_OBJECT             { $$ = smt2_term_const($1); }
| defined_plain_term          { $$ = $1; }

defined_plain_term :
  atomic_defined_word         { 
                                T_SORT sort_ptr = smt2_sort_lookup(strmake("U"));
                                if (!get_is_tff())
                                  smt2_declare_fun(strmake($1), NULL, sort_ptr);
                                $$ = smt2_term($1); 
                              }
| atomic_defined_word '(' arguments ')' 
                              { 
                                char * def_func;
                                tptp_check_defined_functor($1, yy3lineno);
                                tptp_to_smt($1, yy3lineno, &def_func);
                                if (def_func == NULL)
                                  veriT_error("parse_tptp: defined_type not recognized");
                                else
                                  $$ = smt2_term_app(def_func, $3);
                                free($1);
                              }

/* FD defined_plain_formula */
defined_plain_term_prop :
  atomic_defined_word         { 
                                if (strcmp($1,"$true") && strcmp($1,"$false") )
                                  veriT_error("parse_tptp: defined_constant unknown");
                                if (!strcmp($1,"$true"))
                                  $$ = smt2_term(strmake("true"));
                                else
                                  $$ = smt2_term(strmake("false"));
                                free($1);
                              }
| atomic_defined_word '(' arguments ')' 
                              { 
                                char * def_func;
                                tptp_check_defined_predicates($1, yy3lineno);
                                tptp_to_smt($1, yy3lineno, &def_func);
                                if (def_func == NULL)
                                  veriT_error("parse_tptp: defined function not recognized");
                                else
                                  {
                                    $$ = smt2_term_app(def_func, $3);
                                  }
                                free($1);
                              }

system_term :
  atomic_system_word          { 
                                T_SORT sort_ptr = smt2_sort_lookup(strmake("Bool"));
                                smt2_declare_fun(strmake($1), NULL, sort_ptr);
                                $$ = smt2_term($1); 
                              } 
| atomic_system_word '(' arguments ')' 
                              { 
                                T_SORT sort_ptr = smt2_sort_lookup(strmake("Bool"));
                                $$ = tptp_define_term_fun($1, $3, sort_ptr);
                              }

arguments :
  term                        { $$ = smt2_term_list_one($1); }
| term ',' arguments          { $$ = smt2_term_list_add($3, $1); }

conditional_term :
  "$ite_t" '(' tff_logic_formula ',' term ',' term ')' 
                              { 
                                T_TERM_LIST term_list = smt2_term_list_one($3);
                                term_list = smt2_term_list_add(term_list, $5);
                                term_list = smt2_term_list_add(term_list, $7);
                                $$ = smt2_term_app(strmake("ite"), term_list); 
                              }

let_term :
  "$let_ft" '(' tff_let_formula_defn ',' term ')'  
                              { tptp_error_not_implemented("$let_ft", yy3lineno); }
| "$let_tt" '(' tff_let_term_defn ',' term ')'   
                              { tptp_error_not_implemented("$let_tt", yy3lineno); }


/* FD Formula sources */
source :
  general_term                { }

/* FD Useful info fields */
optional_info :
  ',' useful_info             { }
| /* FD empty */              { }

useful_info :
  general_list                { }

general_term :
  general_data                { }
| general_data ':'  general_term
                              { }
| general_list                { }

/* FD expand the following general_data rule
general_data:
TK_LIT_BIND '(' VARIABLE ',' formula_data ')' {  }
*/

general_data :
  atomic_word                 { }
| general_function            { }
| VARIABLE                    { }
| number                      { }
| DISTINCT_OBJECT             { }
| formula_data                { }

general_function :
  atomic_word '(' general_terms ')'                
                              { }

formula_data :
  "$tff" '(' tff_formula ')'  { }
| "$fof" '(' fof_formula ')'  { }
| "$cnf" '(' cnf_formula ')'  { }
| "$fot" '(' term ')'         { }

general_list :
  '[' ']'                     { }
| '[' general_terms ']'       { }

general_terms :
  general_term                { }
| general_term ',' general_terms
                              { }

/* First non terminal level */
name :
  atomic_word                 { $$ = $1; }
| INTEGER                     { $$ = $1; }

atomic_word :
  LOWER_WORD                  { $$ = $1; }
| SINGLE_QUOTED               { $$ = $1; }

atomic_defined_word :
  DOLLAR_WORD                 { $$ = $1; }

atomic_system_word :
  DOLLAR_DOLLAR_WORD          { }

number : 
  INTEGER                     { $$ = tptp_define_term_number($1); }                             
| RATIONAL                    { 
                                char * split_pos = strchr($1, '/');
                                char *fst = malloc(1 + sizeof(char)*((unsigned)(split_pos - $1)));
                                char *snd;
                                T_TERM term_fst, term_snd;
                                strncpy(fst, $1, (unsigned)(split_pos - $1));
                                fst[split_pos - $1]=0;
                                snd = strmake(1+split_pos);
                                term_fst = tptp_define_term_number(fst);
                                term_snd = tptp_define_term_number(snd);
                                $$ = tptp_binary_term(term_fst, term_snd, strmake("/"));
                                free($1);
                              }
| REAL                        { 
                                if(strstr($1, "E") != NULL) 
                                  tptp_error_not_implemented("Exponential", yy3lineno);
                                $$ = tptp_define_term_number($1); 
                              }
                                      
%%

/*--------------------------------------------------------------*/

extern void initlex(char *arg);

extern FILE *yyin;

void
parse_tptp(FILE * input, char * filename, bool option_disable_print_success)
{
#ifdef DEBUG_PARSER
  yydebug = 1;
#endif
  yylineno = 1;
  yyin = input;
  if (!yyin)
    veriT_error("parse_smtlib2: no input file");

  /* FD initialization of veriT data structures */
  smt2_init(option_disable_print_success);

  /* FD set flag in order to know if the functions symbols must be defined or not */
  set_is_tff(0);

  /* FD define the logic for TPTP translation */
  smt2_set_logic(strmake("AUFLIRA"));

  /* FD define nonempty set of "objects" of some kind to use for First Order Logic (one typed) */
  smt2_declare_sort(strmake("U"), strmake("0"));

  /* FD initialization list of variables read while parsing formulas CNF */
  stack_var = smt2_stack_var_new();

  /* FD parsing initialization */
  yyinitfile(filename);
  yyparse();

  /* FD free the path to axioms */
  free_axiom_path();

  printf("Check SAT\n");
  /* FD checking satistiability and finishing execution */
  smt2_check_sat(); 

  /* FD release list of CNF variables */
  free(stack_var);

  smt2_done();
  yylex_destroy();
}
