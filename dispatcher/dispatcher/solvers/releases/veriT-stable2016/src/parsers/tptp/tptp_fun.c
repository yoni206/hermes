/*
  Ver. 1.0 - 20131202
  author Federico Dobal
*/

#include "response.h"

#include "smtfun.h"
#include "tptp_fun.h"

/**
   \brief constant string to identify unidentified TPTP symbols into SMT2-LIB */
#define UNDEFINED "ND"

unsigned is_tff = 0;

/*--------------------------------------------------------------*/

void
tptp_set_formula_status(char * comment_status_line)
{
  char * st;
  st=strchr(comment_status_line,':')+2;
  if (!strcmp(st, "Satisfiable") ) 
    smt2_set_info_str(strmake(":status"), strmake("sat"));
  else if (!strcmp(st, "Unsatisfiable") ) 
    smt2_set_info_str(strmake(":status"), strmake("unsat"));
  else
    smt2_set_info_str(strmake(":status"), strmake("unknown"));
}

/*--------------------------------------------------------------*/

void 
tptp_define_formula_role(T_TERM term, char * role, int line_nro)
{
  /* FD set defined role to false (not found) */
  unsigned defined_role = 0;
  unsigned i;
  const char * roles[] = {"axiom", "hypothesis", "definition", "assumption", 
                                "lemma", "theorem", "conjecture", "negated_conjecture", 
                                "plain", "fi_domain", "fi_functors", "fi_predicates", "type" };
  /* FD loop to find the role received within the TPTP roles */
   for (i=0;  i < sizeof(roles) / sizeof(roles[0]) && !defined_role; i++)
    if (!strcmp(role, roles[i]))
    {
      defined_role = 1;
      break;
    }
  /* FD check if the role received is a valid role */
  if (!defined_role)
    veriT_error("parse_tptp: line %d: Formula role unknown", line_nro);
  /* FD if there is no error, execute formula assertion */
  if (strcmp(role,"type"))
    smt2_assert(term);
  free(role);
}

/*--------------------------------------------------------------*/

void 
tptp_declare_function(char * name, T_TERM_LIST args, T_SORT sort)
{
  unsigned i;
  unsigned l = list_length(args);
  T_SORT_LIST list_sorts = smt2_sort_list_new();
  if (is_tff)
    return;
  for (i = 0; i < l; i++)
    {
      T_TERM t = (T_TERM)(intptr_t) list_n(args, (int) i);
      T_SORT sort = (T_SORT)(intptr_t) DAG_sort(t);
      list_sorts = smt2_sort_list_add(list_sorts, sort);
    }
  smt2_declare_fun(name, list_sorts, sort);
}

/*--------------------------------------------------------------*/

T_TERM 
tptp_define_term_fun(char * name, T_TERM_LIST args, T_SORT sort)
{
  char *name_app = tptp_conv_reserved_word(name);
  tptp_declare_function(name_app, args, sort);
  return smt2_term_app(name_app, args);
}

/*--------------------------------------------------------------*/

T_TERM 
tptp_binary_term(T_TERM t_1, T_TERM t_2, char * func_name)
{
  T_TERM_LIST term_list;
  term_list = smt2_term_list_one(t_1);
  term_list = smt2_term_list_add(term_list, t_2);
  return smt2_term_app(func_name, term_list); 
}

/*--------------------------------------------------------------*/

T_TERM 
tptp_define_term_app_const(char * name, char * name_1, T_SORT sort_1, T_TERM term_two)
{
  T_TERM term_1;
  /* FD if name_1 is an SMT2-LIB reserved word it is renamed */
  name_1 = tptp_conv_reserved_word(name_1);
  if (!is_tff)
    smt2_declare_fun(strmake(name_1), NULL, sort_1);
  term_1 = smt2_term(name_1); 
  return tptp_binary_term(term_1, term_two, name);
}

/*--------------------------------------------------------------*/

T_TERM 
tptp_define_term_app_fun(char * name, char * name_1, T_SORT sort_1, T_TERM_LIST args,  T_TERM term_two)
{
  T_TERM term_1;
  /* FD if name_1 is an SMT2-LIB reserved word it is renamed */
  name_1 = tptp_conv_reserved_word(name_1);
  tptp_declare_function(name_1, args, sort_1);
  /* FD build the function term just defined */
  term_1 = smt2_term_app(name_1, args);
  return tptp_binary_term(term_1, term_two, name);
}

/*--------------------------------------------------------------*/

T_TERM
tptp_define_binary_formula(T_TERM fst, T_TERM snd, char * conn)
{
  T_TERM t_1, t_2, fst_dup, snd_dup;
  if (!(strcmp(conn, "iff")) || !(strcmp(conn, "<~>")))
    {
      fst_dup = DAG_dup(fst);
      snd_dup = DAG_dup(snd);
      /* FD from left to right */
      t_1 = tptp_binary_term(fst, snd, strmake("=>"));
      /* FD from right to left */
      t_2 = tptp_binary_term(snd_dup, fst_dup, strmake("=>"));
      /* FD AND */
      return tptp_binary_term(t_1, t_2, strmake("and"));
    } 
  if (!(strcmp(conn, "=>")))
    {
      /* FD left to right implies */
       return tptp_binary_term(fst, snd, strmake("=>"));
    }
  if (!(strcmp(conn, "<=")))
    {
      /* FD right to left implies */
      return tptp_binary_term(snd, fst, strmake("=>"));
    }
  if (!(strcmp(conn, "~|")))
    {
      t_1 = tptp_binary_term(fst, snd, strmake("or"));
      return smt2_term_app(strmake("not"), smt2_term_list_one(t_1));
    }
  if (!(strcmp(conn, "~&")))
    {
      t_1 = tptp_binary_term(fst, snd, strmake("and"));
      return smt2_term_app(strmake("not"), smt2_term_list_one(t_1));
    }  
  veriT_error("parse_tptp: binary_connective [%s] unknown", conn);
  return 0;
}

/*--------------------------------------------------------------*/

T_TERM
tptp_define_term_number(char * number)
{
  char *unsigned_num, *op;
  T_TERM term_fst, term_snd;
  /* FD if the number received is negative */
  if (number[0] == '+' || number[0] == '-')
    {
      /* FD save the sign to build the signed term */
      op = "+";
      if (number[0] == '-')
        op = strmake("-");
      /* FD split the number in tokens */
      unsigned_num = strtok(number, "+-");
      term_fst = smt2_term_const(strmake("0"));
      term_snd = smt2_term_const(strmake(unsigned_num));
      free(number);
      return tptp_binary_term(term_fst, term_snd, op);
    }
  return smt2_term_const(number);  
}

/*--------------------------------------------------------------*/

char *
tptp_conv_reserved_word(char * func_name)
{
  unsigned i;
  const char * smt2_words[] =
    { "true", "false", "not", "and", "or", "xor", "distinct", "ite", "let",
      "exists", "forall", "to_real", "to_int", "is_int", "abs", "div", "mod",
      "select", "store", "lambda", "apply" };
  /* FD loop to find out whether func_name is a SMT2-LIB reserved word */
  for (i = 0; i < sizeof(smt2_words) / sizeof(smt2_words[0]); i++)
    if (!strcmp(func_name, smt2_words[i]))
      {
        size_t sz = 0;
        char * ret = strapp(NULL, &sz, func_name);
        return strapp(ret, &sz, "_tp");
      }
  /* FD check whether indeed func_name is a SMT2-LIB reserved word */
  return strmake(func_name);
}

/*--------------------------------------------------------------*/

void
tptp_check_defined_type(char * type_name, int line_nro)
{
  if (strcmp(type_name, "$real")  &&
      strcmp(type_name, "$rat")   &&
      strcmp(type_name, "$int")   &&
      strcmp(type_name, "$i")     && 
      strcmp(type_name, "$iType") &&
      strcmp(type_name, "$o")     && 
      strcmp(type_name, "$oType") &&
      strcmp(type_name, "$tType"))
    veriT_error("parse_tptp: defined_type [%s] unknown on line %d", type_name, line_nro);
}

/*--------------------------------------------------------------*/

void
tptp_check_defined_functor(char * fun_name, int line_nro)
{
  /* FD set defined functor to false (not found) */
  unsigned defined_functor = 0;
  unsigned i;
  const char * functors[] = { "$uminus",      "$sum",         "$difference", "$product", 
                              "$quotient",    "$quotient_e",  "$quotient_t", "$quotient_f", 
                              "$remainder_e", "$remainder_t", "$remainder_f", 
                              "$floor",       "$ceiling",     "$truncate",   "$round", 
                              "$to_int",      "$to_rat",      "$to_real" };
  /* FD loop to find the functor name received within the TPTP defined functors */
  for (i=0;  i < sizeof(functors) / sizeof(functors[0]) && !defined_functor; i++)
    if (!strcmp(fun_name, functors[i]))
      {
        defined_functor = 1;
        break;
      }
  /* FD check if the functor received is a valid functor name */
  if (!defined_functor)
    veriT_error("parse_tptp: defined functor [%s] unknown on line %d", fun_name, line_nro);
}

/*--------------------------------------------------------------*/

void
tptp_check_defined_predicates(char * pred_name, int line_nro)
{
  /* FD set defined predicate to false (not found) */
  unsigned defined_pred = 0;
  unsigned i;
  const char * predicates[] = { "$distinct", 
                                      "$less", "$lesseq", "$greater", "$greatereq", 
                                      "$is_int", "$is_rat" };
  /* FD loop to find the predicate name received within the TPTP defined predicates */
  for (i=0;  i < sizeof(predicates) / sizeof(predicates[0]) && !defined_pred; i++)
    if (!strcmp(pred_name, predicates[i]))
      {
        defined_pred = 1;
        break;
      }
  /* FD check if the predicate received is a valid functor name */
  if (!defined_pred)
    veriT_error("parse_tptp: defined predicate [%s] unknown on line %d", pred_name, line_nro);
}


/*--------------------------------------------------------------*/

void
tptp_to_smt(char * tptpDefinedName, int line_nro, char ** ret)
{
  unsigned i;
  char* pTemp;
  const char * tptp_smt2 [25][2] = { /* FD defined arithmetic symbols (18 symbols) */
                               {"$uminus",      "-"},
                               {"$sum",         "+"},
                               {"$difference",  "-"},
                               {"$product",     "*"},
                               {"$quotient",    "div"},
                               {"$quotient_e",  UNDEFINED},
                               {"$quotient_t",  UNDEFINED},
                               {"$quotient_f",  UNDEFINED},
                               {"$remainder_e", UNDEFINED}, 
                               {"$remainder_t", UNDEFINED},  
                               {"$remainder_f", UNDEFINED}, 
                               {"$floor",       "floor"},
                               {"$ceiling",     UNDEFINED},
                               {"$truncate",    UNDEFINED},
                               {"$round",       UNDEFINED},
                               {"$to_int",      "to_int"},
                               {"$to_rat",      UNDEFINED},
                               {"$to_real",     "to_real"},
                               /* FD defined boolean functions (predicates) (7 symbols) */
                               {"$distinct",    "distinct"},
                               {"$less",        "<"},
                               {"$lesseq",      "<="},
                               {"$greater",     ">"},
                               {"$greatereq",   ">="},
                               {"$is_int",      UNDEFINED},
                               {"$is_rat",      UNDEFINED}
                             };
  for (i=0;  i < 25; i++)
    if (!strcmp(tptpDefinedName, tptp_smt2[i][0]))
      {
        pTemp = strmake(tptp_smt2[i][1]);
        strcpy(pTemp, tptp_smt2[i][1]);
        *ret = pTemp;
        break;
      }
  if (!strcmp(*ret, UNDEFINED))
    {
      tptp_error_not_implemented(tptpDefinedName, line_nro);
    }
  return;
}

/*--------------------------------------------------------------*/

void tptp_error_not_implemented(char *symbol, int line_nro)
{
  veriT_error("parse_tptp: tptp symbol [%s] not yet implemented on line %d", symbol, line_nro);
}

/*--------------------------------------------------------------*/

void tptp_error(char * msg, char *symbol_0, char *symbol_1, int line_nro)
{
  veriT_error(msg, symbol_0, symbol_1, line_nro);
}

/*--------------------------------------------------------------*/
