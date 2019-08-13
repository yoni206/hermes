/* -*- mode: C -*- */

/* PF adds clauses C to database, and returns literal such that
   literal corresponds to DAG
   pols is either
     POLARITY_POS if DAG is only used positively
     POLARITY_NEG if DAG is only used negatively
     POLARITY_BOTH if DAG is used with both polarities */
static Tlit
VAR_CNF(TDAG DAG, Tpolarity polarities)
{
  Tlit lit;
  Tpolarity missing_polarities = polarities;
  assert(polarities);
#ifdef DEBUG_CNF
  fprintf(stderr, "var_cnf (pol %d) : ", polarities);
  DAG_fprint(stderr, DAG);
  fprintf(stderr, "\n");
#endif
  if (DAG_symb(DAG) == CONNECTOR_NOT)
    return lit_neg(VAR_CNF(DAG_arg0(DAG), inverse_polarities(polarities)));
  lit = cnf_DAG_to_literal(DAG);
  missing_polarities = polarities & (~cnf_literal_polarities(lit));
  if (!missing_polarities)
    return lit;
  cnf_literal_add_polarities(lit, missing_polarities);

  if (DAG_symb(DAG) == BOOLEAN_TRUE)
    {
      Tclause clause = clause_new(1);
      clause->lits[0] = lit;
      clause_push_proof(clause, proof_true());
      cnf_literal_add_polarities(lit, POLARITY_BOTH);
    }
  else if (DAG_symb(DAG) == BOOLEAN_FALSE)
    {
      Tclause clause = clause_new(1);
      clause->lits[0] = lit_neg(lit);
      clause_push_proof(clause, proof_false());
      cnf_literal_add_polarities(lit, POLARITY_BOTH);
    }
  else if (!boolean_connector(DAG_symb(DAG)))
    {
    }
  else if (DAG_symb(DAG) == CONNECTOR_AND)
    {
      unsigned i;
      Tclause clause;
      if (missing_polarities & POLARITY_POS)
	{
	  for (i = 0; i < DAG_arity(DAG); i++)
	    {
	      clause = clause_new(2);
	      clause->lits[0] = VAR_CNF(DAG_arg(DAG, i), missing_polarities);
	      clause->lits[1] = lit_neg(lit);
	      clause_push_proof(clause, proof_and_pos(DAG, i));
	    }
	}
      if (missing_polarities & POLARITY_NEG)
	{
	  clause = clause_new(DAG_arity(DAG) + 1);
	  for (i = 0; i < DAG_arity(DAG); i++)
	    clause->lits[i] =
	      lit_neg(VAR_CNF(DAG_arg(DAG, i), missing_polarities));
	  clause->lits[i] = lit;
	  clause_push_proof(clause, proof_and_neg(DAG));
	}
    }
  else if (DAG_symb(DAG) == CONNECTOR_OR)
    {
      unsigned i;
      Tclause clause;
      if (missing_polarities & POLARITY_POS)
	{
	  clause = clause_new(DAG_arity(DAG) + 1);
	  for (i = 0; i < DAG_arity(DAG); i++)
	    clause->lits[i] = VAR_CNF(DAG_arg(DAG, i), missing_polarities);
	  clause->lits[i] = lit_neg(lit);
	  clause_push_proof(clause, proof_or_pos(DAG));
	}
      if (missing_polarities & POLARITY_NEG)
	{
	  for (i = 0; i < DAG_arity(DAG); i++)
	    {
	      clause = clause_new(2);
	      clause->lits[0] = lit_neg(VAR_CNF(DAG_arg(DAG, i),
						missing_polarities));
	      clause->lits[1] = lit;
	      clause_push_proof(clause, proof_or_neg(DAG, i));
	    }
	}
    }
  else if (DAG_symb(DAG) == CONNECTOR_XOR)
    {
      /* PF we can safely assume arity = 2.
	 Otherwise rewritten as preprocessing */
      assert(DAG_arity(DAG) == 2);
      if (missing_polarities & POLARITY_POS)
	{
	  Tclause clause = clause_new(3);
	  clause->lits[0] = VAR_CNF(DAG_arg0(DAG), POLARITY_BOTH);
	  clause->lits[1] = VAR_CNF(DAG_arg1(DAG), POLARITY_BOTH);
	  clause->lits[2] = lit_neg(lit);
	  clause_push_proof(clause, proof_xor_pos1(DAG));
	  clause = clause_new(3);
	  clause->lits[0] = lit_neg(VAR_CNF(DAG_arg0(DAG), POLARITY_BOTH));
	  clause->lits[1] = lit_neg(VAR_CNF(DAG_arg1(DAG), POLARITY_BOTH));
	  clause->lits[2] = lit_neg(lit);
	  clause_push_proof(clause, proof_xor_pos2(DAG));
	}
      if (missing_polarities & POLARITY_NEG)
	{
	  Tclause clause = clause_new(3);
	  clause->lits[0] = VAR_CNF(DAG_arg0(DAG), POLARITY_BOTH);
	  clause->lits[1] = lit_neg(VAR_CNF(DAG_arg1(DAG), POLARITY_BOTH));
	  clause->lits[2] = lit;
	  clause_push_proof(clause, proof_xor_neg1(DAG));
	  clause = clause_new(3);
	  clause->lits[0] = lit_neg(VAR_CNF(DAG_arg0(DAG), POLARITY_BOTH));
	  clause->lits[1] = VAR_CNF(DAG_arg1(DAG), POLARITY_BOTH);
	  clause->lits[2] = lit;
	  clause_push_proof(clause, proof_xor_neg2(DAG));
	}
    }
  else if (DAG_symb(DAG) == CONNECTOR_IMPLIES)
    {
      if (missing_polarities & POLARITY_POS)
	{
	  Tclause clause = clause_new(3);
	  clause->lits[0] =
	    lit_neg(VAR_CNF(DAG_arg0(DAG),
			    inverse_polarities(missing_polarities)));
	  clause->lits[1] = VAR_CNF(DAG_arg1(DAG), missing_polarities);
	  clause->lits[2] = lit_neg(lit);
	  clause_push_proof(clause, proof_implies_pos(DAG));
	}
      if (missing_polarities & POLARITY_NEG)
	{
	  Tclause clause = clause_new(2);
	  clause->lits[0] = VAR_CNF(DAG_arg0(DAG), POLARITY_POS);
	  clause->lits[1] = lit;
	  clause_push_proof(clause, proof_implies_neg1(DAG));
	  clause = clause_new(2);
	  clause->lits[0] = lit_neg(VAR_CNF(DAG_arg1(DAG), POLARITY_NEG));
	  clause->lits[1] = lit;
	  clause_push_proof(clause, proof_implies_neg2(DAG));
	}
    }
  else if (DAG_symb(DAG) == CONNECTOR_EQUIV)
    {
      if (missing_polarities & POLARITY_POS)
	{
	  Tclause clause = clause_new(3);
	  clause->lits[0] = VAR_CNF(DAG_arg0(DAG), POLARITY_BOTH);
	  clause->lits[1] = lit_neg(VAR_CNF(DAG_arg1(DAG), POLARITY_BOTH));
	  clause->lits[2] = lit_neg(lit);
	  clause_push_proof(clause, proof_equiv_pos1(DAG));
	  clause = clause_new(3);
	  clause->lits[0] = lit_neg(VAR_CNF(DAG_arg0(DAG), POLARITY_BOTH));
	  clause->lits[1] = VAR_CNF(DAG_arg1(DAG), POLARITY_BOTH);
	  clause->lits[2] = lit_neg(lit);
	  clause_push_proof(clause, proof_equiv_pos2(DAG));
	}
      if (missing_polarities & POLARITY_NEG)
	{
	  Tclause clause = clause_new(3);
	  clause->lits[0] = lit_neg(VAR_CNF(DAG_arg0(DAG), POLARITY_BOTH));
	  clause->lits[1] = lit_neg(VAR_CNF(DAG_arg1(DAG), POLARITY_BOTH));
	  clause->lits[2] = lit;
	  clause_push_proof(clause, proof_equiv_neg1(DAG));
	  clause = clause_new(3);
	  clause->lits[0] = VAR_CNF(DAG_arg0(DAG), POLARITY_BOTH);
	  clause->lits[1] = VAR_CNF(DAG_arg1(DAG), POLARITY_BOTH);
	  clause->lits[2] = lit;
	  clause_push_proof(clause, proof_equiv_neg2(DAG));
	}
    }
  else if (DAG_symb(DAG) == CONNECTOR_ITE)
    {
      if (missing_polarities & POLARITY_POS)
	{
	  Tclause clause = clause_new(3);
	  clause->lits[0] = VAR_CNF(DAG_arg(DAG, 0), POLARITY_BOTH);
	  clause->lits[1] = VAR_CNF(DAG_arg(DAG, 2), missing_polarities);
	  clause->lits[2] = lit_neg(lit);
	  clause_push_proof(clause, proof_ite_pos1(DAG));
	  clause = clause_new(3);
	  clause->lits[0] = lit_neg(VAR_CNF(DAG_arg(DAG, 0), POLARITY_BOTH));
	  clause->lits[1] = VAR_CNF(DAG_arg(DAG, 1), missing_polarities);
	  clause->lits[2] = lit_neg(lit);
	  clause_push_proof(clause, proof_ite_pos2(DAG));
	}
      if (missing_polarities & POLARITY_NEG)
	{
	  Tclause clause = clause_new(3);
	  clause->lits[0] = VAR_CNF(DAG_arg(DAG, 0), POLARITY_BOTH);
	  clause->lits[1] = lit_neg(VAR_CNF(DAG_arg(DAG, 2), missing_polarities));
	  clause->lits[2] = lit;
	  clause_push_proof(clause, proof_ite_neg1(DAG));
	  clause = clause_new(3);
	  clause->lits[0] = lit_neg(VAR_CNF(DAG_arg(DAG, 0), POLARITY_BOTH));
	  clause->lits[1] = lit_neg(VAR_CNF(DAG_arg(DAG, 1), missing_polarities));
	  clause->lits[2] = lit;
	  clause_push_proof(clause, proof_ite_neg2(DAG));
	}
    }
#ifdef DEBUG_CNF
  fprintf(stderr, "VAR_CNF %d for formula : ", lit);
  DAG_fprint(stderr, DAG);
  fprintf(stderr, "\n");
#endif
  return lit;
}

/*--------------------------------------------------------------*/

/* PF adds clauses C to database, such that
   (C sat) iff (DAG sat) if pol == POLARITY_POS
   (C sat) iff (not DAG sat) if pol == POLARITY_NEG
   If def is 0, normal form is p-definitional.
   Definitional otherwise */
static void
SILENT_CNF(TDAG DAG, Tpolarity pol, int def PROOF_ARG(Tproof proof))
{
  Tclause clause;
  assert(polarities);
  assert(pol == POLARITY_POS || pol == POLARITY_NEG);
#ifdef DEBUG_CNF
  fprintf(stderr, "silent_cnf (pol %d, def %d)\n", pol, def);
  DAG_fprint(stderr, DAG);
  fprintf(stderr, "\n");
#endif
  if (!boolean_connector(DAG_symb(DAG)))
    {
      clause = clause_new(1);
      if (pol == POLARITY_POS)
	clause->lits[0] = VAR_CNF(DAG, def ? POLARITY_BOTH : pol);
      else
	clause->lits[0] = lit_neg(VAR_CNF(DAG, def ? POLARITY_BOTH : pol));
      clause_push_proof(clause, proof);
    }
  else if (DAG_symb(DAG) == CONNECTOR_NOT)
    {
      if (pol == POLARITY_POS)
	SILENT_CNF(DAG_arg0(DAG), POLARITY_NEG, def PROOF_ARG(proof));
      else
	SILENT_CNF(DAG_arg0(DAG), POLARITY_POS, def PROOF_ARG(proof));
#if 0
	SILENT_CNF(DAG_arg0(DAG), POLARITY_POS, def
		   PROOF_ARG(proof_not_not(proof)));
#endif
    }
  else if (DAG_symb(DAG) == CONNECTOR_AND && pol == POLARITY_POS)
    {
      unsigned i;
      for (i = 0; i < DAG_arity(DAG); i++)
	SILENT_CNF(DAG_arg(DAG, i), POLARITY_POS, def
		   PROOF_ARG(proof_and(proof, i)));
    }
  else if (DAG_symb(DAG) == CONNECTOR_OR && pol == POLARITY_NEG)
    {
      unsigned i;
      for (i = 0; i < DAG_arity(DAG); i++)
	SILENT_CNF(DAG_arg(DAG, i), POLARITY_NEG, def
		   PROOF_ARG(proof_not_or(proof, i)));
    }
  else if (DAG_symb(DAG) == CONNECTOR_AND && pol == POLARITY_NEG)
    {
      unsigned i;
      clause = clause_new(DAG_arity(DAG));
      for (i = 0; i < DAG_arity(DAG); i++)
	clause->lits[i] = lit_neg(VAR_CNF(DAG_arg(DAG, i),
					  def ? POLARITY_BOTH : pol));
      clause_push_proof(clause, proof_not_and(proof));
    }
  else if (DAG_symb(DAG) == CONNECTOR_OR && (pol == POLARITY_POS))
    {
      unsigned i;
      clause = clause_new(DAG_arity(DAG));
      for (i = 0; i < DAG_arity(DAG); i++)
	clause->lits[i] = VAR_CNF(DAG_arg(DAG, i), def ? POLARITY_BOTH : pol);
      clause_push_proof(clause, proof_or(proof));
    }
  else if (DAG_symb(DAG) == CONNECTOR_XOR)
    {
      /* PF we can safely assume arity = 2.
	 Otherwise rewritten as preprocessing */
      assert(DAG_arity(DAG) == 2);
      if (pol == POLARITY_POS)
	{
	  Tclause clause = clause_new(2);
	  clause->lits[0] = VAR_CNF(DAG_arg0(DAG), POLARITY_BOTH);
	  clause->lits[1] = VAR_CNF(DAG_arg1(DAG), POLARITY_BOTH);
	  clause_push_proof(clause, proof_xor1(proof));
	  clause = clause_new(2);
	  clause->lits[0] = lit_neg(VAR_CNF(DAG_arg0(DAG), POLARITY_BOTH));
	  clause->lits[1] = lit_neg(VAR_CNF(DAG_arg1(DAG), POLARITY_BOTH));
	  clause_push_proof(clause, proof_xor2(proof));
	}
      else
	{
	  Tclause clause = clause_new(2);
	  clause->lits[0] = lit_neg(VAR_CNF(DAG_arg0(DAG), POLARITY_BOTH));
	  clause->lits[1] = VAR_CNF(DAG_arg1(DAG), POLARITY_BOTH);
	  clause_push_proof(clause, proof_not_xor2(proof));
	  clause = clause_new(2);
	  clause->lits[0] = VAR_CNF(DAG_arg0(DAG), POLARITY_BOTH);
	  clause->lits[1] = lit_neg(VAR_CNF(DAG_arg1(DAG), POLARITY_BOTH));
	  clause_push_proof(clause, proof_not_xor1(proof));
	}
    }
  else if (DAG_symb(DAG) == CONNECTOR_IMPLIES)
    {
      if (pol == POLARITY_POS)
	{
	  clause = clause_new(2);
	  clause->lits[0] =
	    lit_neg(VAR_CNF(DAG_arg0(DAG), def ? POLARITY_BOTH : POLARITY_NEG));
	  clause->lits[1] =
	    VAR_CNF(DAG_arg1(DAG), def ? POLARITY_BOTH : POLARITY_POS);
	  clause_push_proof(clause, proof_implies(proof));
	}
      else
	{
	  SILENT_CNF(DAG_arg0(DAG), POLARITY_POS, def
		     PROOF_ARG(proof_not_implies1(proof)));
	  SILENT_CNF(DAG_arg1(DAG), POLARITY_NEG, def
		     PROOF_ARG(proof_not_implies2(proof)));
	}
    }
  else if (DAG_symb(DAG) == CONNECTOR_EQUIV)
    {
      clause = clause_new(2);
      if (pol == POLARITY_POS)
	{
	  clause->lits[0] = lit_neg(VAR_CNF(DAG_arg0(DAG), POLARITY_BOTH));
	  clause->lits[1] = VAR_CNF(DAG_arg1(DAG), POLARITY_BOTH);
	  clause_push_proof(clause, proof_equiv1(proof));
	  clause = clause_new(2);
	  clause->lits[0] = VAR_CNF(DAG_arg0(DAG), POLARITY_BOTH);
	  clause->lits[1] = lit_neg(VAR_CNF(DAG_arg1(DAG), POLARITY_BOTH));
	  clause_push_proof(clause, proof_equiv2(proof));
	}
      else
	{
	  clause->lits[0] = VAR_CNF(DAG_arg0(DAG), POLARITY_BOTH);
	  clause->lits[1] = VAR_CNF(DAG_arg1(DAG), POLARITY_BOTH);
	  clause_push_proof(clause, proof_not_equiv1(proof));
	  clause = clause_new(2);
	  clause->lits[0] = lit_neg(VAR_CNF(DAG_arg0(DAG), POLARITY_BOTH));
	  clause->lits[1] = lit_neg(VAR_CNF(DAG_arg1(DAG), POLARITY_BOTH));
	  clause_push_proof(clause, proof_not_equiv2(proof));
	}
    }
  else if (DAG_symb(DAG) == CONNECTOR_ITE)
    {
      clause = clause_new(2);
      if (pol == POLARITY_POS)
	{
	  clause->lits[0] = VAR_CNF(DAG_arg(DAG, 0), POLARITY_BOTH);
	  clause->lits[1] =
	    VAR_CNF(DAG_arg(DAG, 2), def ? POLARITY_BOTH : POLARITY_POS);
	  clause_push_proof(clause, proof_ite1(proof));
	  clause = clause_new(2);
	  clause->lits[0] = lit_neg(VAR_CNF(DAG_arg(DAG, 0), POLARITY_BOTH));
	  clause->lits[1] =
	    VAR_CNF(DAG_arg(DAG, 1), def ? POLARITY_BOTH : POLARITY_POS);
	  clause_push_proof(clause, proof_ite2(proof));
	}
      else
	{
	  clause->lits[0] = VAR_CNF(DAG_arg(DAG, 0), POLARITY_BOTH);
	  clause->lits[1] =
	    lit_neg(VAR_CNF(DAG_arg(DAG, 2), def ? POLARITY_BOTH : POLARITY_NEG));
	  clause_push_proof(clause, proof_not_ite1(proof));
	  clause = clause_new(2);
	  clause->lits[0] = lit_neg(VAR_CNF(DAG_arg(DAG, 0), POLARITY_BOTH));
	  clause->lits[1] =
	    lit_neg(VAR_CNF(DAG_arg(DAG, 1), def ? POLARITY_BOTH : POLARITY_NEG));
	  clause_push_proof(clause, proof_not_ite2(proof));
	}
    }
}

/*
  --------------------------------------------------------------
  Public functions
  --------------------------------------------------------------
*/

void
PROOF_FCT(cnf)(TDAG DAG, Tstack_clause * Pclauses PROOF_ARG(Tproof proof))
{
#if STATS_LEVEL > 1
  int cnf_pdef_n;
  int cnf_binary_n;
#endif
#ifdef DEBUG_CNF
  unsigned i;
#endif
  assert(polarities);
  PclausesL = Pclauses;
  SILENT_CNF(DAG, 1, cnf_definitional ? 1 : 0 PROOF_ARG(proof));

#if STATS_LEVEL > 1
  cnf_pdef_n = stack_size(*Pclauses);
  cnf_binary_n = cnf_binary_count(*Pclauses);
  stats_counter_set(stat_n_pdef, cnf_pdef_n);
  stats_counter_set(stat_n_binary, cnf_binary_n);
#endif

#ifdef DEBUG_CNF
  fprintf(stderr, "CNF RESULT : \n");
  for (i = 0; i < stack_size(*Pclauses); ++i)
    clause_symbolic_fprint(stderr, stack_get(*Pclauses, i));
  fprintf(stderr, "END OF CNF\n");
#endif
#ifdef STATS_CNF
  if (cnf_stats)
    statistics(stderr);
#endif
}
