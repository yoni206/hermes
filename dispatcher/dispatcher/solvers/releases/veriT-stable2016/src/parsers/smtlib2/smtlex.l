/*
  SMT-lib lexical file
  Ver. 1.0 - 20050323
  Updated  - 20080901
  Ver. 2.0 - 20100507
  Pascal Fontaine
*/
%{

/* #define DEBUG_PARSER */
#include <string.h>
#include <stdio.h>

#include "general.h"
#
#include "parser_macro.h"

#include "smtfun.h"
#include "smtsyn.h"

#define yydebug yy2debug
#define yyerror yy2error
/* #define yyin yy2in */

#define MAX_BUFFER_LENGTH 4096

static int nb_in_mybuffer = 0;
static char mybuffer[MAX_BUFFER_LENGTH];
#define CHECK_MY_BUFFER \
  if (++nb_in_mybuffer >= MAX_BUFFER_LENGTH)			\
    {								\
      my_error("string or annotation overflow on line %d\n",	\
	       yylineno);					\
    }
char * Pchar; 

#ifdef DEBUG_PARSER
extern int yydebug;
#endif
extern void yyerror(char *s);

%}

%x start_string
%x start_user_value
%option yylineno
%option noyywrap

NUMERAL         0|[1-9][0-9]*
/* PF Change RATIONAL --> DECIMAL */
DECIMAL         {NUMERAL}\.[0-9]+
HEXADECIMAL     #x[0-9A-Fa-f]+
BINARY          #b[01]+
/* PF STRING is defined later */
/* PF !$^&_. */
SP_CHAR         "+"|"-"|"/"|"*"|"="|"%"|"?"|"!"|"."|"$"|"_"|"~"|"&"|"^"|"<"|">"|"@"|"'"
/* PF "'" is an addition to SMT-LIB 2.0 language */
CHAR            {SP_CHAR}|[a-zA-Z]
SYMBOL_NAME     {CHAR}({CHAR}|[0-9])*
SYMBOL_STRING   \|[^\|]*\|
SYMBOL          {SYMBOL_NAME}|{SYMBOL_STRING}
KEYWORD         \:{SYMBOL_NAME}

%%

	/* PF Predefined symbols (See Appendix B) */

"as"				{ return TK_AS ; }
"assert"			{ return TK_ASSERT ; }
"background"			{ return TK_BACKGROUND ; }
"Bool"				{ return TK_BOOL ; }
"check-sat"			{ return TK_CHECK_SAT ; }
"continued-execution"		{ return TK_CONTINUED_EXECUTION ; }
"declare-fun"			{ return TK_DECLARE_FUN ; }
"declare-sort"			{ return TK_DECLARE_SORT ; }
"define-fun"			{ return TK_DEFINE_FUN ; }
"define-sort"			{ return TK_DEFINE_SORT ; }
"distinct"			{ yylval.string = (char *) strmake(yytext);
                                  return SYMBOL; }
"error"				{ return TK_ERROR ; }
"exists"			{ return TK_EXISTS ; }
"exit"				{ return TK_EXIT ; }
"false"				{ return TK_FALSE ; }
"forall"			{ return TK_FORALL ; }
"get-assertions"		{ return TK_GET_ASSERTIONS ; } /* PF was not in the text */
"get-assignment"		{ return TK_GET_ASSIGNMENT ; }
"get-info"			{ return TK_GET_INFO ; }
"get-model"			{ return TK_GET_MODEL ; } /* PF was not in the text */
"get-option"			{ return TK_GET_OPTION ; } /* PF Not in predifined symbols */
"get-proof"			{ return TK_GET_PROOF ; }
"get-unsat-core"		{ return TK_GET_UNSAT_CORE ; }
"get-value"			{ return TK_GET_VALUE ; }
"immediate-exit"		{ return TK_IMMEDIATE_EXIT ; }
"incomplete"			{ return TK_INCOMPLETE ; }
"let"				{ return TK_LET ; }
"logic"				{ return TK_LOGIC ; }
"none"			  	{ return TK_NONE ; }
"NUMERAL"			{ return TK_NUMERAL ; }
"memout"			{ return TK_MEMOUT ; }
"par"				{ return TK_PAR ; }
"pop"				{ return TK_POP ; }
"push"				{ return TK_PUSH ; }
"DECIMAL"			{ return TK_DECIMAL ; }
"set-info"			{ return TK_SET_INFO ; }
"set-logic"			{ return TK_SET_LOGIC ; }
"set-option"			{ return TK_SET_OPTION ; }
"STRING"			{ return TK_STRING ; }
"theory"			{ return TK_THEORY ; }
"true"				{ return TK_TRUE ; }
"unsupported"			{ return TK_UNSUPPORTED ; }
                /* lambda expression extension */
"@lambda"			{ return TK_LAMBDA ; }


		/* interpreted attributes */
":named"                        { return TK_NAMED ; }
":pattern"                      { return TK_PATTERN ; }

	/*"="	| */
"("	|
")"	{ return yytext[0]; }

";".*\n		{ ; }

\n		{ ; }
\r		{ ; }
[ \t]		{ ; }

	/* PF Tokens (See Appendix B) */

{NUMERAL}       { yylval.string = (char *) strmake(yytext);
#ifdef DEBUG_PARSER
		  if (yydebug) fprintf(stderr, "lex NUMERAL [%s]\n",yytext);
#endif
                  return NUMERAL; }

{DECIMAL}       { yylval.string = (char *) strmake(yytext);
#ifdef DEBUG_PARSER
		  if (yydebug) fprintf(stderr, "lex DECIMAL [%s]\n",yytext);
#endif
                  return DECIMAL; }

{HEXADECIMAL}	{ yylval.string = (char *) strmake(yytext);
#ifdef DEBUG_PARSER
		  if (yydebug) fprintf(stderr, "lex HEXADECIMAL [%s]\n",yytext);
#endif
                  return HEXADECIMAL; }

{BINARY}	{ yylval.string = (char *) strmake(yytext);
#ifdef DEBUG_PARSER
		  if (yydebug) fprintf(stderr, "lex BINARY [%s]\n",yytext);
#endif
                  return BINARY; }

\"              { Pchar = mybuffer; nb_in_mybuffer = 0;
		  CHECK_MY_BUFFER; *Pchar++ = '"';
		  BEGIN(start_string); }
<start_string>{
  \\\"          { CHECK_MY_BUFFER; *Pchar++ = '"'; }
  [^\"\n]       { CHECK_MY_BUFFER; *Pchar++ = yytext[0]; }
  \n            { CHECK_MY_BUFFER; *Pchar++ = '\n'; }
  \"            { CHECK_MY_BUFFER; *Pchar++ = '"';
		  CHECK_MY_BUFFER; *Pchar = '\0';
  		  yylval.string = (char *) strmake(mybuffer);
                  BEGIN(INITIAL); return STRING; }
}

{SYMBOL}	{ 
                  if (strcmp(yytext, "!") == 0)
                    return TK_BANG;
                  else if (strcmp(yytext, "_") == 0)
                    return TK_UNDERSCORE;
 	          else
                    {
                      yylval.string = (char *) strmake(yytext);
#ifdef DEBUG_PARSER
		  if (yydebug) fprintf(stderr, "lex SYMBOL [%s]\n",yytext);
#endif
                      return SYMBOL; 
                    }
                  }

{KEYWORD}	{ yylval.string = (char *) strmake(yytext);
#ifdef DEBUG_PARSER
		  if (yydebug) fprintf(stderr, "lex KEYWORD [%s]\n",yytext);
#endif
                  return KEYWORD; }

. { my_error("syntax error on line %d : [%s]\n",yylineno, yytext); }

	/* PF these remained form SMT-LIB 1.2, that may be again harcoded for 2.0
"and"		{ return TK_AND ; }
"if_then_else"	{ return TK_IF_THEN_ELSE ; }
"iff"		{ return TK_IFF ; }
"implies"	{ return TK_IMPLIES ; }
"ite"		{ return TK_ITE ; }
"not"		{ return TK_NOT ; }
"or"		{ return TK_OR ; }
"true"		{ return TK_TRUE ; }
"unknown"	{ return TK_UNKNOWN ; }
"unsat" 	{ return TK_UNSAT ; }
"xor"		{ return TK_XOR ; }
*/

%%
