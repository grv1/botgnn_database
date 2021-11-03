/*
 * test_postgres.c
 * test the library
 */

#include <stdio.h>
#include <stdlib.h>
#include <libpq-fe.h>

static void
exit_nicely(PGconn *conn) 
{
  PQfinish(conn);
  exit(1);
}

int
main(int argc, char **argv)
{
  const char *conn_info;
  PGconn *conn;
  PGresult *res;

  int nFields;
  int i, j;


  if (argc > 1)
    conn_info = argv[1];
  else
    conn_info = "dbname = test";

  conn = PQconnectdb(conn_info);

  if (PQstatus(conn) != CONNECTION_OK)
    {
      fprintf(stderr, "Connection to database failed: %s", PQerrorMessage(conn));
      exit_nicely(conn);
    }

  res = PQexec(conn, "BEGIN");
  if (PQresultStatus(res) != PGRES_COMMAND_OK)
    {
      fprintf(stderr, "BEGIN command failed: %s", PQerrorMessage(conn));
      PQclear(res);
      exit_nicely(conn);
    }

  PQclear(res);

  res = PQexec(conn, "DECLARE myportal CURSOR FOR select * from pg_database");
  if (PQresultStatus(res) != PGRES_COMMAND_OK)
    {
      fprintf(stderr, "DECLARE command failed: %s", PQerrorMessage(conn));
      PQclear(res);
      exit_nicely(conn);
    }

  res = PQexec(conn, "FETCH ALL in myportal");
  if (PQresultStatus(res) != PGRES_TUPLES_OK)
    {
      fprintf(stderr, "FETCH command failed: %s", PQerrorMessage(conn));
      PQclear(res);
      exit_nicely(conn);
    }

  nFields = PQnfields(res);
  for (i=0; i<nFields; ++i)
    printf("%-15s", PQfname(res,i));
  printf("\n\n");

  for (i=0; i<PQntuples(res); ++i)
    {
      for (j=0; j<nFields; ++j)
	printf("%-15s", PQgetvalue(res, i, j));
      printf("\n");
    }

  PQclear(res);

  res = PQexec(conn, "CLOSE myportal");
  PQclear(res);

  PQfinish(conn);

  return 0;
  
}
