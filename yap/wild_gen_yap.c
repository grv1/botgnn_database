#include "wild_gen_pyc.h"

#define DEBUG 1

static int
set_bottom_clause(void) 
{
  char *task_name;
  int result;

  YAP_Term task = YAP_ARG1;
  if (DEBUG) printf("Got the YAP term\n");

  YAP_Atom task_atom = YAP_AtomOfTerm(task);
  task_name = YAP_AtomName(task_atom);
  if (DEBUG) printf("I will set a new bottom clause for %s\n", task_name);

  result = run_wild_gen(task_name);
  if(result) return TRUE;
  else return FALSE;
}

static int
my_process_id(void)
{
  YAP_Term pid = YAP_MkIntTerm(getpid());
  YAP_Term out = YAP_ARG1;
  return (YAP_Unify(out,pid));
}

void
init_my_predicates()
{
  YAP_UserCPredicate("my_process_id",my_process_id,1);
  YAP_UserCPredicate("hcb_set_bc",set_bottom_clause,2);
}
