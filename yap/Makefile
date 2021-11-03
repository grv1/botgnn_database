WILD_HDRS = wild_gen_pyc.h wild_aleph_interface.h
WILD_SRCS = wild_gen_yap.c wild_gen_pyc.c wild_aleph_interface.c
WILD_OBJS = wild_gen_yap.o wild_gen_pyc.o wild_aleph_interface.o 

YAP_DIR = /Users/hcorrada/WILD/yap/yap-4.5.3
PYTHON_LIB = -framework Python

SHARE_LIB_FLAGS = -flat_namespace -bundle -undefined suppress
PYTHON_SHARE_LIB_FLAGS = -u __dummy -u _PyMac_Error -framework System -framework Python -framework CoreServices -framework Foundation

all: wild_gen_lib

wild_gen_test: $(WILD_OBJS)
	cc -o wild_gen_test -twolevel_namespace -I$(YAP_DIR)/include -L$(YAP_DIR)/lib $(WILD_OBJS) -lYap -lreadline $(PYTHON_SHARE_LIB_FLAGS)

wild_gen_lib: $(WILD_OBJS)
	cc -flat_namespace -bundle -undefined suppress -o wild_gen_yap.so $(WILD_OBJS) $(PYTHON_SHARE_LIB_FLAGS) 

wild_gen_yap.o: wild_gen_yap.c
	cc -c -I$(YAP_DIR)/include wild_gen_yap.c

wild_aleph_interface.o: wild_aleph_interface.c wild_aleph_interface.h
	cc -c -I$(YAP_DIR)/include wild_aleph_interface.c

wild_gen_pyc.o: wild_gen_pyc.c wild_gen_pyc.h
	cc -c -I$(YAP_DIR)/include wild_gen_pyc.c

my_process.so: my_process.o
	cc $(SHARE_LIB_FLAGS) -o my_process.so my_process.o $(PYTHON_SHARE_LIB_FLAGS)

my_process.o: my_process.c
	cc -c -I$(YAP_DIR)/include my_process.c

test_postgres.o: test_postgres.c
	cc -c -I/usr/local/pgsql/include test_postgres.c

test_pg: test_postgres.o
	cc -o test_pg test_postgres.o -L/usr/local/pgsql/lib -lpq

run_func: run_func.o
	cc -o run_func -framework Python run_func.o 

run_func.o: run_func.c
	cc -c  run_func.c


clean:
	rm *~ *.o test_pg run_func wild_gen.so wild_gen_test
