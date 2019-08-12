/*
  TPTP lexical file
  Ver. 1.0 - 20131202
  Federico Dobal
*/

%{

#include "smtfun.h"
#include "tptpsyn.h"

#define yylineno yy3lineno

/*******************************/
#define yydebug yy3debug
#define yyerror yy3error
/*******************************/

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

/* PF2FD there are too many file names around, couldn't this be simplified? */
/* FD define the structure to use in order to store the include files to parse */
struct bufstack { 
  struct bufstack *prev; 
  YY_BUFFER_STATE bs; 
  int lineno; 
  char *filename; 
  FILE *f; 
} *curbs = 0;

char *curfilename; 

int newfile(char *fn);
int popfile(void);
char * file_name;

/* FD path to axioms */
static char * axioms_path;


%}

%x start_string
%x start_user_value
%x IFILE

%option yylineno
%option noyywrap

/* FD Tokens used in syntax */

NOT_STAR_SLASH           ([^*]*[*][*]*[^/*])*[^*]*
COMMENT_BLOCK            [/][*]{NOT_STAR_SLASH}[*][*]*[/]
COMMENT_LINE             "%".*

PERCENTAGE_SIGN          [%]
DOUBLE_QUOTE             [\"]
SINGLE_QUOTE             [\']
DO_ESCAPE                [^\\"]|[\\]["]|[\\][\\]
SQ_ESCAPE                [^\\']|[\\][']|[\\][\\]
SP_CHAR                  "!"|"#"|"%"|"&"|"("|")"|"*"|"+"|","|"-"|"."|"/"|":"|";"|"<"|"="|">"|"?"|"@"|"["|"]"|"^"|"_"|"`"|"{"|"|"|"}"|"~"|"$"
SIGN                     [+-]
DOT                      [.]
EXPONENT                 [Ee]
SLASH                    [/]
ZERO_NUMERIC             [0]
NON_ZERO_NUMERIC         [1-9]
NUMERIC                  [0-9]
LOWER_ALPHA              [a-z]
UPPER_ALPHA              [A-Z]
ALPHA_NUMERIC            {LOWER_ALPHA}|{UPPER_ALPHA}|{NUMERIC}|[_]
DOLLAR                   [$]
PRINTABLE_CHAR           .

LOWER_WORD               {LOWER_ALPHA}{ALPHA_NUMERIC}*
UPPER_WORD               {UPPER_ALPHA}{ALPHA_NUMERIC}*
VARIABLE                 {UPPER_WORD}
DOLLAR_WORD              {DOLLAR}{LOWER_WORD}*
DOLLAR_DOLLAR_WORD       {DOLLAR}{DOLLAR}{LOWER_WORD}*
DO_CHAR                  {SP_CHAR}|{DO_ESCAPE}|{SINGLE_QUOTE}|{ALPHA_NUMERIC}
DISTINCT_OBJECT          {DOUBLE_QUOTE}{DO_CHAR}*{DOUBLE_QUOTE}
SQ_CHAR                  {SP_CHAR}|{SQ_ESCAPE}|{DOUBLE_QUOTE}|{ALPHA_NUMERIC}|" "
SINGLE_QUOTED            {SINGLE_QUOTE}{SQ_CHAR}{SQ_CHAR}*{SINGLE_QUOTE}

DECIMAL                  {ZERO_NUMERIC}|{POSITIVE_DECIMAL}
POSITIVE_DECIMAL         {NON_ZERO_NUMERIC}{NUMERIC}*
DECIMAL_EXPONENT         ({DECIMAL}|{DECIMAL_FRACTION}){EXPONENT}{INTEGER}
DECIMAL_FRACTION         {DECIMAL}{DOT_DECIMAL}
DOT_DECIMAL              {DOT}{NUMERIC}{NUMERIC}*
UNSIGNED_REAL            {DECIMAL_FRACTION}|{DECIMAL_EXPONENT}
SIGNED_REAL              {SIGN}{UNSIGNED_REAL}
REAL                     {SIGNED_REAL}|{UNSIGNED_REAL}
UNSIGNED_RATIONAL        {DECIMAL}{SLASH}{POSITIVE_DECIMAL}
SIGNED_RATIONAL          {SIGN}{UNSIGNED_RATIONAL}
RATIONAL                 {SIGNED_RATIONAL}|{UNSIGNED_RATIONAL}
UNSIGNED_INTEGER         {DECIMAL}
SIGNED_INTEGER           {SIGN}{UNSIGNED_INTEGER}
INTEGER                  {SIGNED_INTEGER}|{UNSIGNED_INTEGER}

%%

 /* FD token identification */

"!>"                            { return TK_EXCLAMATION_ARROW; }   
"?*"                            { return TK_QUESTION_STAR; }   
"@+"                            { return TK_PLUS_ARROBA; }   
"@-"                            { return TK_MINUS_ARROBA; }   
"!!"                            { return TK_DOUBLE_EXCLAMATION; }   
"??"                            { return TK_DOUBLE_QUESTION; }   
"<=>"                           { return TK_IFF; }   
 "=>"                           { return TK_RIGHT_IMP; }   
"<="                            { return TK_LEFT_IMP; }   
"<~>"                           { return TK_EQUIV; }   
"~&"                            { return TK_NEG_AMPERSAND; }   
"-->"                           { return TK_GENTZEN_ARROW; }   
"!="                            { return TK_INFIX_INEQUALITY; }
"<<"                            { return TK_SUBTYPE_SIGN; }

"!"	                        |
"?"	                        |
"~"	                        |
"&"	                        |
"="	                        |
"|"	                        |
"*"	                        |
"+"	                        |
">"	                        |
"<"	                        |
":"	                        |
"["	                        |
"]"	                        |
"@"	                        |
"."	                        |
","	                        |
"("	                        |
")"	                        { return yytext[0]; }
"tpi"                           { return TK_TPI;}
"thf"                           { my_error("tptp_error: thf formulas not supported yet.\n"); }
"tff"                           { return TK_TFF;}
"fof"                           { return TK_FOF;}
"cnf"                           { return TK_CNF;}

"include"[ \t]*\({SINGLE_QUOTE} { BEGIN IFILE; }

<IFILE>{SQ_CHAR}{SQ_CHAR}*      { /* FD read include token, so restart the parser */
                                  int c;
                                  size_t sz = 0;
                                  while ((c=input()) && c != '\n');
                                  /* FD set the path to the axiom file */
                                  char * axiom_file = strapp(NULL, &sz, NULL);
                                  axiom_file = strapp(axiom_file, &sz, axioms_path);
                                  axiom_file = strapp(axiom_file, &sz, yytext);
                                  /* FD put the axiom file in the axiom files stack */
                                  if (!newfile(axiom_file))
                                    /* FD no such file */
                                    my_error("tptp_parser could not be initialized\n%s: No such file or directory\n", yytext); 
                                  free(axiom_file);
                                  /* FD change to initial state to restart the parsing */                              
                                  BEGIN INITIAL;
                                }    

"$ite_f"                        { return TK_ITE_F; }
"$let_tf"                       { my_error("tptp_error: let_tf not supported yet because of thf formulas.\n"); }
"$let_ff"                       { my_error("tptp_error: let_ff not supported yet because of thf formulas.\n"); }
"$ite_t"                        { return TK_ITE_T; }
"$let_ft"                       { return TK_LET_FT; }
"$let_tt"                       { return TK_LET_TT; }

" "                             |
\n		                { ; }

 /* FD Tokens used in syntax */

{COMMENT_LINE}           { yy3lval.string = strmake(yytext);
#ifdef DEBUG_PARSER
		           if (yydebug) fprintf(stderr, "lex SINGLE_QUOTE [%s]\n",yytext);
#endif
                           return TK_COMMENT_LINE; }
{COMMENT_BLOCK}          { yy3lval.string = strmake(yytext);
#ifdef DEBUG_PARSER
		           if (yydebug) fprintf(stderr, "lex SINGLE_QUOTE [%s]\n",yytext);
#endif
                           return TK_COMMENT_BLOCK; }

{DISTINCT_OBJECT}        { yy3lval.string = strmake(yytext);
#ifdef DEBUG_PARSER
		           if (yydebug) fprintf(stderr, "lex DISTINCT_OBJECT [%s]\n",yytext);
#endif
                           return DISTINCT_OBJECT; }
               
{SINGLE_QUOTED}          { yy3lval.string = strmake(yytext);
#ifdef DEBUG_PARSER
		           if (yydebug) fprintf(stderr, "lex SINGLE_QUOTE [%s]\n",yytext);
#endif
                           return SINGLE_QUOTED; }


{VARIABLE}               { yy3lval.string = strmake(yytext);
#ifdef DEBUG_PARSER
		           if (yydebug) fprintf(stderr, "lex VARIABLE [%s]\n",yytext);
#endif
                           return VARIABLE; }

{LOWER_WORD}             { yy3lval.string = strmake(yytext);
#ifdef DEBUG_PARSER
		           if (yydebug) fprintf(stderr, "lex LOWER_WORD [%s]\n",yytext);
#endif
                           return LOWER_WORD; }

{DOLLAR_WORD}            { yy3lval.string = strmake(yytext);
#ifdef DEBUG_PARSER
		           if (yydebug) fprintf(stderr, "lex DOLLAR_WORD [%s]\n",yytext);
#endif
                           return DOLLAR_WORD; }

{DOLLAR_DOLLAR_WORD}     { yy3lval.string = strmake(yytext);
#ifdef DEBUG_PARSER
		           if (yydebug) fprintf(stderr, "lex DOLLAR_DOLLAR_WORD [%s]\n",yytext);
#endif
                           return DOLLAR_DOLLAR_WORD; }


{REAL}                   { yy3lval.string = strmake(yytext);
#ifdef DEBUG_PARSER
		           if (yydebug) fprintf(stderr, "lex REAL DEBUG [%s]\n",yytext);
#endif
                           return REAL; }

{RATIONAL}               { yy3lval.string = strmake(yytext);
#ifdef DEBUG_PARSER
		           if (yydebug) fprintf(stderr, "lex RATIONAL DEBUG [%s]\n",yytext);
#endif
                           return RATIONAL; }

{INTEGER}                { yy3lval.string = strmake(yytext);
#ifdef DEBUG_PARSER
		           if (yydebug) fprintf(stderr, "lex INTEGER DEBUG [%s]\n",yytext);
#endif
                           return INTEGER; }


{PRINTABLE_CHAR}         { my_error("syntax error on line %d : [%s]\n",yylineno, yytext); }

<<EOF>>                  { if (!popfile()) yyterminate(); }

%%

/*--------------------------------------------------------------*/

void 
yy3initfile(char *fn)
{
  char * split_pos;
  /* FD Set the path to axioms. 
        The parser assumes the instances are stored in a directory 
        with at least two subdirectories Problems and Axioms.
  */
  file_name = strmake(fn);
  split_pos = strstr(file_name,"Problems");
  if (split_pos != 0)
    {
      axioms_path = malloc(1 + sizeof(char) * (split_pos-file_name));
      strncpy(axioms_path, file_name, split_pos - file_name);
      axioms_path[split_pos-file_name]=0;
    } else {
      axioms_path = strmake("");
    }
  free(file_name);
  /* FD first file to parse is the instance itself */
  if (!newfile(fn))
    my_error("parse_tptp: parser could not be initialized");
}

/*--------------------------------------------------------------*/

int
newfile(char *fn)
{
  FILE *f = fopen(fn, "r");
  struct bufstack *bs = malloc(sizeof(struct bufstack));
  /* FD	 die if no file or no room */
  if (!f)
    {
      perror(fn);
      return 0;
    }
  if (!bs) { perror("malloc"); exit(1); }
  /* FD remember state */
  if (curbs)
    curbs->lineno = yylineno;
  bs->prev = curbs;
  /* FD set up current entry */
  bs->bs = yy_create_buffer(f, YY_BUF_SIZE);
  bs->f = f;
  bs->filename = fn;
  yy_switch_to_buffer(bs->bs);
  curbs = bs;
  yylineno = 1;
  curfilename = fn;
  return 1;
}

/*--------------------------------------------------------------*/
/* PF2FD if there is a pop, there should be a push: try to clean */
int
popfile(void)
{
  struct bufstack *bs = curbs;
  struct bufstack *prevbs;
  if (!bs) 
    return 0;
  /* FD get rid of current entry */
  fclose(bs->f);
  yy_delete_buffer(bs->bs);
  /* FD switch back to previous */
  prevbs = bs->prev;
  free(bs);
  if (!prevbs)
    return 0;
  yy_switch_to_buffer(prevbs->bs);
  curbs = prevbs;
  yylineno = curbs->lineno;
  curfilename = curbs->filename;
  return 1;
}

/*--------------------------------------------------------------*/

/* PF2FD is it necessary to have to call this from outside? */
void 
free_axiom_path(void)
{
  free(axioms_path);
}
