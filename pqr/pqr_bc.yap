:- eraseall(lits).
:- eraseall(ivars).
:- eraseall(ovars).
:- recorda(lits, lit_info(-1,0,junk,[],[],[]),_).
:- recorda(ivars, ivars(-1,[]),_).
:- recorda(ovars, ovars(-1,[]),_).
:- recordz(lits, lit_info(1,0,p(1),[],[[1]/any],[2, 3]),_).
:- recordz(ivars, ivars(1,[]),_).
:- recordz(ovars, ovars(1,[1]),_).
:- recordz(lits, lit_info(2,0,q(1,2),[[1]/any],[[2]/any],[4, 5, 6]),_).
:- recordz(ivars, ivars(2,[1]),_).
:- recordz(ovars, ovars(2,[2]),_).
:- recordz(lits, lit_info(3,0,q(1,3),[[1]/any],[[2]/any],[4, 7, 5, 8, 6, 9]),_).
:- recordz(ivars, ivars(3,[1]),_).
:- recordz(ovars, ovars(3,[3]),_).
:- recordz(lits, lit_info(4,0,r1(2),[[1]/any],[],[9]),_).
:- recordz(ivars, ivars(4,[2]),_).
:- recordz(ovars, ovars(4,[]),_).
:- recordz(lits, lit_info(5,0,r2(2),[[1]/any],[],[]),_).
:- recordz(ivars, ivars(5,[2]),_).
:- recordz(ovars, ovars(5,[]),_).
:- recordz(lits, lit_info(6,0,r4(2),[[1]/any],[],[]),_).
:- recordz(ivars, ivars(6,[2]),_).
:- recordz(ovars, ovars(6,[]),_).
:- recordz(lits, lit_info(7,0,r1(3),[[1]/any],[],[6]),_).
:- recordz(ivars, ivars(7,[3]),_).
:- recordz(ovars, ovars(7,[]),_).
:- recordz(lits, lit_info(8,0,r2(3),[[1]/any],[],[]),_).
:- recordz(ivars, ivars(8,[3]),_).
:- recordz(ovars, ovars(8,[]),_).
:- recordz(lits, lit_info(9,0,r4(3),[[1]/any],[],[]),_).
:- recordz(ivars, ivars(9,[3]),_).
:- recordz(ovars, ovars(9,[]),_).
:- wild_reset_db_entry(sat,bot_size,10).
:- wild_reset_db_entry(sat,last_lit,15).
:- wild_reset_db_entry(sat,last_var,3).
:- wild_reset_db_entry(sat,head_ivars,[1]).
:- wild_reset_db_entry(sat,head_ovars,[]).
