#include "Yap/YapInterface.h"
#import <Python/Python.h>

#define DEBUG 1

// declaration
int wild_pred_to_aleph_lit(PyObject *predicate, PyObject* children);
int wild_clear_literals();
YAP_Term wild_pylist_to_yaplist(PyObject *list);
