#include <stdlib.h>
#include <stdio.h>

#include "veriT-SAT.h"

int
main(void)
{
  SAT_Tlit * clause;
  SAT_Tstatus status;
  // initialize
  SAT_init();
  // SAT_var_new_id allows to notify SAT solver of the ids of variables
  SAT_var_new_id(1);
  SAT_var_new_id(2);
  SAT_var_new_id(3);
  /* An example set of clauses:
      1  2  3 0
     -1  2  3 0
      1 -2  3 0
     -1 -2  3 0
      1  2 -3 0
     -1  2 -3 0
      1 -2 -3 0
     -1 -2 -3 0
  */
  /* Adding clauses :  1  2  3 0 */
  clause = (SAT_Tlit*) malloc(3 * sizeof(SAT_Tlit));
  clause[0] = SAT_lit(1, 1);
  clause[1] = SAT_lit(2, 1);
  clause[2] = SAT_lit(3, 1);
  SAT_clause_new(3, clause);
  /* Adding clauses : -1  2  3 0 */
  clause = (SAT_Tlit*) malloc(3 * sizeof(SAT_Tlit));
  clause[0] = SAT_lit(1, 0);
  clause[1] = SAT_lit(2, 1);
  clause[2] = SAT_lit(3, 1);
  SAT_clause_new(3, clause);
  /* Adding clauses :  1 -2  3 0 */
  clause = (SAT_Tlit*) malloc(3 * sizeof(SAT_Tlit));
  clause[0] = SAT_lit(1, 1);
  clause[1] = SAT_lit(2, 0);
  clause[2] = SAT_lit(3, 1);
  SAT_clause_new(3, clause);
  /* Adding clauses : -1 -2  3 0 */
  clause = (SAT_Tlit*) malloc(3 * sizeof(SAT_Tlit));
  clause[0] = SAT_lit(1, 0);
  clause[1] = SAT_lit(2, 0);
  clause[2] = SAT_lit(3, 1);
  SAT_clause_new(3, clause);
  /* Adding clauses :  1  2 -3 0 */
  clause = (SAT_Tlit*) malloc(3 * sizeof(SAT_Tlit));
  clause[0] = SAT_lit(1, 1);
  clause[1] = SAT_lit(2, 1);
  clause[2] = SAT_lit(3, 0);
  SAT_clause_new(3, clause);
  /* Adding clauses : -1  2 -3 0 */
  clause = (SAT_Tlit*) malloc(3 * sizeof(SAT_Tlit));
  clause[0] = SAT_lit(1, 0);
  clause[1] = SAT_lit(2, 1);
  clause[2] = SAT_lit(3, 0);
  SAT_clause_new(3, clause);
  /* Adding clauses :  1 -2 -3 0 */
  clause = (SAT_Tlit*) malloc(3 * sizeof(SAT_Tlit));
  clause[0] = SAT_lit(1, 1);
  clause[1] = SAT_lit(2, 0);
  clause[2] = SAT_lit(3, 0);
  SAT_clause_new(3, clause);
  /* Adding clauses : -1 -2 -3 0 */
  clause = (SAT_Tlit*) malloc(3 * sizeof(SAT_Tlit));
  clause[0] = SAT_lit(1, 0);
  clause[1] = SAT_lit(2, 0);
  clause[2] = SAT_lit(3, 0);
  SAT_clause_new(3, clause);

  status = SAT_solve();
  if (status == SAT_STATUS_SAT)
    {
      unsigned i;
      printf("satisfiable\n");
      for (i = 1; i <=3; i++)
	printf("Value of variable %d: %d\n", i, SAT_var_value(i)?1:-1);
    }
  else if (status == SAT_STATUS_UNSAT)
    printf("unsatisfiable\n");
  // SAT_status remembers the returned status
  // release
  SAT_done();
  return 0;
}
