#include "wild_aleph_interface.h"

int 
wild_pred_to_aleph_lit(PyObject *predicate, PyObject *children)
{
  YAP_Term yap_children;

  if (DEBUG) printf("Entered predicate to lit convertor.\n");

  /* make children term */
  yap_children = wild_pylist_to_yaplist(children);
  Py_DECREF(children);
  if (DEBUG) printf("Children list converted.\n");

  /* make output term */
  /* make input term */
  /* make atom term */
  /* make depth term */
  /* make litnum term */
  /* make litinfo term */
  /* insert to database */

  if (DEBUG) printf("Exiting predicate to lit convertor.\n");
  return 1;
}

int
wild_clear_literals()
{
  return 1;
}

YAP_Term
wild_pylist_to_yaplist(PyObject *list)
{
  YAP_Term result;
  int num_elements,i;
  long c_element;
  YAP_Term yap_element;
  PyObject *py_element;

  if (DEBUG) printf("Entered list convertor.\n");
  result = YAP_MkAtomTerm(YAP_LookupAtom("[]"));
  if (DEBUG) printf("Emtpy list created.\n");

  /* make sure its a list */
  if (!(PyList_Check(list))) {
    fprintf(stderr, "Error in wild_pylist_to_yaplist: Argument is not a list.\n");
    return NULL;
  }
  
  /* iterate through python list */
  num_elements = PyList_Size(list);
  if (DEBUG) printf("list has %d elements.\n", num_elements);

  for (i=num_elements-1; i>=0; --i) {
    py_element = PyList_GetItem(list, i);
    if (DEBUG) printf("Have py element.\n");

    if (!(PyInt_Check(py_element))) {
      fprintf(stderr, "Error: wild_pylist_to_yaplist: Element is not an int\n");
      return NULL;
    }

    c_element = PyInt_AsLong(py_element);
    if (DEBUG) printf("Have c element: %ld.\n",c_element);
    
    yap_element = YAP_MkIntTerm(c_element);
    if (DEBUG) printf("Have yap element.\n");
    result = YAP_MkPairTerm(yap_element, result);
  }
  return result;
}
