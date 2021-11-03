wild_reset_db_entry(Db,Lit, Value) :-
	functor(T,Lit,1),
	recorded(Db, T, DbRef),
	erase(DbRef),
	NewT =.. [Lit, Value],
	recordz(Db, NewT, _).