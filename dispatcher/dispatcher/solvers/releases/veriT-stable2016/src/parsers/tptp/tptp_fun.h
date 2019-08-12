/*
  Ver. 1.0 - 20131202
  author Federico Dobal
*/

#ifndef TPTP_FUN_H
#define TPTP_FUN_H

/**
   \brief flag to be aware if the function symbol has been already defined. 
   \      Used in cnf and fof which functions symbols must be defined
   \      on the fly */
extern unsigned is_tff;

/*
  --------------------------------------------------------------
  FD TPTP functions helpers definitions
  --------------------------------------------------------------
*/

/**
   \brief given the line describing the formula status, it sets the status
   \      All the possible formula status are descripted in the file Documents/SZSOntology into the TPTP distribution 
   \      They are the following:
   \        Success (SUC), UnsatisfiabilityPreserving (UNP), SatisfiabilityPreserving (SAP), EquiSatisfiable (ESA), 
   \        Satisfiable (SAT), FinitelySatisfiable (FSA), FiniteTheorem (FTH), Theorem (THM), SatisfiableTheorem (STH), 
   \        Equivalent (EQV), TautologousConclusion (TAC), WeakerConclusion (WEC), EquivalentTheorem (ETH), Tautology (TAU), 
   \        WeakerTautologousConclusion (WTC), WeakerTheorem (WTH), ContradictoryAxioms (CAX), 
   \        SatisfiableConclusionContradictoryAxioms (SCA), TautologousConclusionContradictoryAxioms (TCA),
   \        WeakerConclusionContradictoryAxioms (WCA), CounterUnsatisfiabilityPreserving (CUP),
   \        CounterSatisfiabilityPreserving (CSP), EquiCounterSatisfiable (ECS), CounterSatisfiable (CSA),
   \        FinitelyCounterSatisfiable (FCS), CounterTheorem (CTH), SatisfiableCounterTheorem (SCT),
   \        CounterEquivalent (CEQ), UnsatisfiableConclusion (UNC), WeakerCounterConclusion (WCC),
   \        EquivalentCounterTheorem (ECT), FinitelyUnsatisfiable (FUN), Unsatisfiable (UNS),
   \        WeakerUnsatisfiableConclusion (WUC), WeakerCounterTheorem (WCT), NoConsequence (NOC)
   \        SatisfiableCounterConclusionContradictoryAxioms (SCC),
   \        UnsatisfiableConclusionContradictoryAxioms (UCA).
   \      We are going to consider only Satisfiable and Unsatisfiable; all the others states are going to be considered unknown.      
   \param comment_status_line line starting with the string '% Status   :' */
void tptp_set_formula_status(char * comment_status_line);

/**
   \brief given a term and a role in tptp, it defines the assertion
   \      corresponding to each role
   \param term formula to assert
   \param role role name
   \param line number to inform in case of error */
void tptp_define_formula_role(T_TERM, char *, int);

/**
   \brief defines a function given a function name, its parameters and sort 
   \param name function name to define
   \param args arguments list
   \param sort function sort */
void tptp_declare_function(char * name, T_TERM_LIST args, T_SORT sort);

/**
   \brief given a function name declares and defines a term application on that function
   \      on the arguments given
   \param name name of the function
   \param args list of terms
   \param sort_1 sort of the term which is going to be defined
   \return the term defined */
T_TERM tptp_define_term_fun(char *, T_TERM_LIST, T_SORT );

/**
   \brief given two terms and a function name builds a term using
   \      the two terms as parameter of the function
   \param t_1 first term (first func_name argument)
   \param t_2 second term (second func_name argument)
   \param func_name function name
   \return the term defined */
T_TERM tptp_binary_term(T_TERM t_1, T_TERM t_2, char * func_name);

/**
   \brief given a name declares and defines a term application on two other terms
   \      the first term is a constant of the sort given
   \param name name of the term application
   \param name_1 name of the term which need to be defined
   \param sort_1 sort of the term which need to be defined
   \param term_two term already defined 
   \return the term defined */
T_TERM tptp_define_term_app_const(char *, char *, T_SORT, T_TERM);

/**
   \brief given a name, it defines a term application on two other terms
   \      the first term is a function of the sort given and arguments args
   \param name name of the term application
   \param name_1 function name to be defined
   \param sort_1 return sort of the function 
   \param args sort of the term which need to be defined
   \param term_two term already defined 
   \return the term defined */
T_TERM tptp_define_term_app_fun(char *, char *, T_SORT, T_TERM_LIST, T_TERM);

/**
   \brief given two terms and a binary connective returns a new term which connects
   \      the two terms by the connective
   \param fst left hand side term
   \param fst right hand side term
   \param conn binary connective name 
   \return the term defined */
T_TERM tptp_define_binary_formula(T_TERM, T_TERM, char *);

/*
  --------------------------------------------------------------
  FD matching beetwen TPTP symbols and SMT2-LIB symbols
  --------------------------------------------------------------
*/
/**
   \brief given a TPTP defined type name checks if it is a valid one.
   \      Prints an error message if it not the case.
   \param type_name defined TPTP type name 
   \param line_nro current line number */
void tptp_check_defined_type(char * type_name, int line_nro);

/**
   \brief given a TPTP defined functor name checks if it is a valid one.
   \      Prints an error message if it not the case.
   \param fun_name defined TPTP functor name 
   \param line_nro current line number */
void tptp_check_defined_functor(char * fun_name, int line_nro);

/**
   \brief given a TPTP defined predicate name checks if it is a valid one.
   \      Prints an error message if it not the case.
   \param pred_name defined TPTP predicate name 
   \param line_nro current line number */
void tptp_check_defined_predicates(char * pred_name, int line_nro);

/**
   \brief given a defined function name in TPTP return the name to use in SMT 
   \      or NULL if it does not match
   \param tptpDefinedName defined function name in TPTP 
   \return SMT name for TPTP function name */
void tptp_to_smt(char * tptpDefinedName, int line_nro, char ** ret);

/**
   \brief given a number builds a term for this number. 
   \      If the number is negative the term is expressed as (- 0 N)
   \param number number read 
   \return term built */
T_TERM tptp_define_term_number(char * number);

/**
   \brief given a function name checks if it is a SMT2-LIB reserved word
   \      if it is the case change the symbol, otherwise returns the same symbol
   \param func_name function name 
   \return the modified symbol */
char * tptp_conv_reserved_word(char *);


/*
  --------------------------------------------------------------
  FD helpers for parsers
  --------------------------------------------------------------
*/

/*PF2FD: well, at first sight this is pretty dirty
  have to check to make constructive comments to remove this */
#define set_is_tff(v) { is_tff = v; }
#define get_is_tff() is_tff

/*
  --------------------------------------------------------------
  FD error and warning functions
  --------------------------------------------------------------
*/

/**
   \brief wrapper of veriT_error, it only customizes the error message
   \param symbol tptp symbol not yet implemented
   \param line_nro current line number */
void tptp_error_not_implemented(char *symbol, int line_nro);

/**
   \brief wrapper of veriT_error, it only customizes the error message
   \param msg output message
   \param symbol_0 tptp term symbol
   \param symbol_1 tptp term symbol
   \param line_nro current line number */
void tptp_error(char * msg, char *symbol_0, char *symbol_1, int line_nro);

/**
   \brief flex-generated scanner routines used in bison-generated parser */
extern int yy3lex(void);
extern int yy3lex_destroy(void);

/* PF2FD this is quite dirty */
extern void yy3initfile(char *);
extern void free_axiom_path(void);

#endif /* TPTP_FUN */
