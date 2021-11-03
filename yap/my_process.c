#import <Python/Python.h>
#include "Yap/YapInterface.h"

#define DEBUG 1

static int
my_process_id(void)
{
  YAP_Term pid = YAP_MkIntTerm(getpid());
  YAP_Term out = YAP_ARG1;
  return (YAP_Unify(out,pid));
}

static YAP_Term
pylist_to_yaplist(PyObject *list)
{
  YAP_Term result;
  int num_elements,i;
  long c_element;
  YAP_Term yap_element;
  PyObject *py_element;


  if (DEBUG) printf("Entered list convertor.\n");
  result = YAP_MkAtomTerm(YAP_LookupAtom("[]")); 
  if (DEBUG) printf("Emtpy list created.\n");

  /* iterate through python list */
  num_elements = PyList_Size(list);
  if (DEBUG) printf("list has %d elements.\n", num_elements);

  for (i=num_elements-1; i>=0; --i) {
    py_element = PyList_GetItem(list, i);
    if (DEBUG) printf("Have py element.\n");

    c_element = PyInt_AsLong(py_element);
    if (DEBUG) printf("Have c element: %ld.\n",c_element);
    //  Py_DECREF(py_element);

    yap_element = YAP_MkIntTerm(c_element);
    if (DEBUG) printf("Have yap element.\n");
    result = YAP_MkPairTerm(yap_element, result);
  }
  return result;
}

static PyObject*
get_python_list()
{
  PyObject *list, *element;
  list = PyList_New(0);
  
  element = PyInt_FromLong(1);
  PyList_Append(list,element);

  element = PyInt_FromLong(2);
  PyList_Append(list, element);

  element = PyInt_FromLong(3);
  PyList_Append(list,element);

  return list;
}

static int
convert_list(void)
{
  PyObject *py_list;
  YAP_Term yap_list;
  YAP_Term out = YAP_ARG1;

  Py_Initialize();
  py_list = get_python_list();
  yap_list = pylist_to_yaplist(py_list);
  Py_Finalize();
  return (YAP_Unify(out,yap_list));
}

void
init_my_predicates()
{
  YAP_UserCPredicate("my_process_id",my_process_id,1);
  YAP_UserCPredicate("convert_list",convert_list,1);
}
