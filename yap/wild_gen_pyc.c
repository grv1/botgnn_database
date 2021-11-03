#include "wild_gen_pyc.h"

int
run_wild_gen(char *task)
{
  const char *func_name = "main";
  const char *lib_name = "wild_gen";
  PyObject *pName, *pModule, *pFunc;
  PyObject *pDict, *pValue;
  int result;

  Py_Initialize();
  if (DEBUG) printf("Interpreter Initialized\n");

  /*pName = PyString_FromString(lib_name);
  pModule = PyImport_Import(pName);
  if (pModule == NULL) {
    PyErr_Print();
    fprintf(stderr, "Failed to load library module %s", lib_name);
    Py_DECREF(pName);
    return 0;
  }

  if (DEBUG) printf("Library Module %s Loaded\n", lib_name);

  Py_DECREF(pName);
  Py_DECREF(pModule);
  */
  pName = PyString_FromString(task);

  pModule = PyImport_Import(pName);
  Py_DECREF(pName);

  if (DEBUG) printf("Module %s loaded\n", task);

  if (pModule != NULL) {
    pDict = PyModule_GetDict(pModule);
    if (PyDict_Check(pDict)){
      if (DEBUG) printf("Module dictionary is dictionary.\n");
    }

    pFunc = PyDict_GetItemString(pDict, func_name);

    if (pFunc == NULL) {
      if (DEBUG) printf("pFunc is null\n");
    }

    if (PyCallable_Check(pFunc)) {
      if (DEBUG) printf("pFunc is callable\n");
    }

    if (pFunc && PyCallable_Check(pFunc)) {
      if (DEBUG) printf("We have main() to call.\n");
      pValue = PyObject_CallObject(pFunc, NULL);
      if (pValue != NULL) {
	if (DEBUG) printf("Main() has returned.\n");
	result = process_bc(pValue);
	Py_DECREF(pValue);
      }
      else {
	Py_DECREF(pModule);
	PyErr_Print();
	fprintf(stderr, "Call failed.\n");
	return 0;
      }
    }
    else {
      if (PyErr_Occurred())
	PyErr_Print();
      fprintf(stderr, "Cannot find function \"%s\"\n", func_name);
      Py_DECREF(pModule);
      return 0;
    }
    Py_DECREF(pModule);
  }
  else {
    PyErr_Print();
    fprintf(stderr, "Failed to load \"%s\"\n", task);
    return 0;
  }
  Py_Finalize();
  return result;
}

int
process_bc(PyObject* bc)
{
  int num_literals,i,result;
  PyObject *literals;
  PyObject *cur_predicate, *cur_children, *cur_pair;

  literals = PyObject_GetAttrString(bc, "lits");
  /* verify this is a list */
  if (!(PyList_Check(literals))) {
    fprintf(stderr, "Error in process_bc: This is not a list.\n");
    return 0;
  }

  /* clear out alephs bottom clause */
  result = wild_clear_literals();
  if (result == 0) {
    fprintf(stderr, "Error clearing literals in Aleph's database");
    return 0;
  }

  /* iterate through literals */
  num_literals = PyList_Size(literals);
  for (i=1; i<num_literals; ++i) {
    cur_pair = PyList_GetItem(literals, i);
    if (cur_pair == NULL) {
      fprintf(stderr, "Error in process_bc: cur_pair is null.\n");
      return 0;
    }
    cur_predicate = PyTuple_GetItem(cur_pair,0);
    cur_children = PyTuple_GetItem(cur_pair,1);
    Py_DECREF(cur_pair);

    result = wild_pred_to_aleph_lit(cur_predicate, cur_children);
    if (!result) {
      fprintf(stderr, "Error in process_bc: conversion to aleph lit failed for literal %d", i);
      Py_DECREF(cur_predicate);
      Py_DECREF(cur_children);
      return 0;
    }
    //    cur_pred_name = PyObject_GetAttrString(cur_predicate, "name");
    //printf ("Bottom clause predicate %d: %s\n", i, PyString_AsString(cur_pred_name));
    //Py_DECREF(cur_pred_name);
    Py_DECREF(cur_predicate);
    Py_DECREF(cur_children);
  }
  return 1;
}

/**
int
main (int argc, char *argv[])
{
  char *task_name;
  int result;
  
  task_name = argv[1];
  result = run_wild_gen(task_name);
  return 0;
}
*/
