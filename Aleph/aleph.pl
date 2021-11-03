%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% A Learning Engine for Proposing Hypotheses                              %
%                                                                         %
% A L E P H                                                               %
% Version 3    (last modified: Mon Mar 18 12:49:10 GMT 2002)              %
%                                                                         %
% This is the source for Aleph written and maintained                     %
% by Ashwin Srinivasan at Oxford (ashwin@comlab.ox.ac.uk)                 %
%                                                                         %
% Aleph supersedes P-Progol                                               %
%                                                                         %
% It runs under the Yap Prolog system (version 4.1.15 and above).         %
% Yap can be found at: www.cos.ufrj.br/~vitor/Yap/                        %
% Yap must be compiled with -DDEPTH_LIMIT=1                               %
%                                                                         %
% If you obtain this version of Aleph and have not already done so        %
% please subscribe to the Aleph mailing list. You can do this by          %
% mailing majordomo@comlab.ox.ac.uk with the following command in the     %
% body of the mail message: subscribe aleph                               %
%                                                                         %
% Aleph is freely available for academic purposes.                        %
% If you intend to use it for commercial purposes then                    %
% please contact Ashwin Srinivasan first.                                 %
%                                                                         %
% A simple on-line manual is available on the Web at                      %
% www.comlab.ox.ac.uk/oucl/research/areas/machlearn/Aleph/index.html      %
%                                                                         %
%                                                                         %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 
 

:- source.
:- system_predicate(false,false), hide(false).
:- style_check(single_var).
% :- use_module(library(terms)).

aleph_version('3').
aleph_version_date('Mon Mar 18 12:49:10 GMT 2002').
aleph_manual('http://www.comlab.ox.ac.uk/oucl/groups/machlearn/Aleph/index.html').

:-
	nl, nl,
	print('A L E P H'), nl,
	aleph_version(Version), print('Version '), print(Version), nl,
	aleph_version_date(Date), print('Last modified: '), print(Date), nl, nl,
	aleph_manual(Man),
	print('Manual: '),
	print(Man), nl, nl.

:- op(500,fy,#).
:- op(500,fy,*).
:- op(900,xfy,because).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% C O N S T R U C T

% get_atoms(+Preds,+Depth,+MaxDepth,+Last,-LastLit)
% layered generation of ground atoms to add to bottom clause
%	Preds is list of PName/Arity entries obtained from the determinations
%	Depth is current variable-chain depth
%	MaxDepth is maximum allowed variable chain depth (i setting)
%	Last is last atom number so far
%	Lastlit is atom number after all atoms to MaxDepth have been generated
get_atoms([],_,_,Last,Last):- !.
get_atoms(Preds,Depth,MaxDepth,Last,LastLit):-
	Depth =< MaxDepth,
	Depth0 is Depth - 1,
	recorded(terms,terms(_,Depth0,_,_),_),	% new terms generated ?
	!,
	get_atoms1(Preds,Depth,MaxDepth,Last,Last1),
	Depth1 is Depth + 1,
	get_atoms(Preds,Depth1,MaxDepth,Last1,LastLit).
get_atoms(_,_,_,Last,Last).

% auxiliary predicate used by get_atoms/5
get_atoms1([],_,_,Last,Last).
get_atoms1([Pred|Preds],Depth,MaxDepth,Last,LastLit):-
	gen_layer(Pred,Depth),
	flatten(Depth,MaxDepth,Last,Last1),
	get_atoms1(Preds,Depth,MaxDepth,Last1,LastLit).

% flatten(+Depth,+MaxDepth,+Last,-LastLit)
% flatten a set of ground atoms by replacing all in/out terms with variables
%	constants are wrapped in a special term called aleph_const(...)
%	eg suppose p/3 had modes p(+char,+char,#int)
%	then p(a,a,3) becomes p(X,X,aleph_const(3))
% ground atoms to be flattened are assumed to be in the i.d.b atoms
% vars and terms are actually integers which are stored in vars/terms databases
%	so eg above actually becomes p(1,1,aleph_const(3)).
%	where variable 1 stands for term 2 (say) which in turn stands for a
%	Depth is current variable-chain depth
%	MaxDepth is maximum allowed variable chain depth (i setting)
%	Last is last atom number so far
%	Lastlit is atom number after ground atoms here have been flattened
flatten(Depth,MaxDepth,Last,_):-
	retract_all(aleph_dyn,flatten_num(_)),
	recorda(aleph_dyn,flatten_num(Last),_),
	get_next_atom(atom(Lit1,Mode)),
	recorded(aleph_dyn,flatten_num(LastSoFar),DbRef1),
	(Lit1 = not(Lit) -> Negated = true; Lit = Lit1, Negated = false),
	flatten_atom(Depth,MaxDepth,Lit,Negated,Mode,LastSoFar,Last1),
	erase(DbRef1),
	recorda(aleph_dyn,flatten_num(Last1),_),
	fail.
flatten(_,_,_,Last):-
	recorded(aleph_dyn,flatten_num(Last),DbRef2),
	erase(DbRef2), !.

% get_next_atom(-Lit)
% get next ground atom in i.d.b atoms
get_next_atom(Lit1):-
	recorded(atoms,Lit1,DbRef), 
	erase(DbRef).

% flatten_atom(+Depth,+Depth1,+Lit,+Negated,+Mode,+Last,-Last1)
%	update lits database by adding ``flattened atoms''. This involves:
%	replacing ground terms at +/- positions in Lit with variables
%	and wrapping # positions in Lit within a special term stucture
%	Mode contains actual mode and term-place numbers and types for +/-/# 
%	Last is the last literal number in the lits database at present
%	Last1 is the last literal number after the update
flatten_atom(Depth,Depth1,Lit,Negated,Mode,Last,Last1):-
	arg(3,Mode,O), arg(4,Mode,C),
	integrate_args(Depth,Lit,O),
	integrate_args(Depth,Lit,C),
	(Depth = Depth1 -> CheckOArgs = true; CheckOArgs = false),
	flatten_lits(Lit,CheckOArgs,Depth,Negated,Mode,Last,Last1).

% variabilise literals by replacing terms with variables
% if var splitting is on then new equalities are introduced into bottom clause
% if at final i-layer, then literals with o/p args that do not contain at least
% 	one output var from head are discarded
flatten_lits(Lit,CheckOArgs,Depth,Negated,Mode,Last,_):-
	functor(Lit,Name,Arity),
	recorda(aleph_dyn,flatten_lits(Last),_),
	Depth1 is Depth - 1,
	functor(OldFAtom,Name,Arity),
	flatten_lit(Lit,Mode,OldFAtom,_,_),
	functor(FAtom,Name,Arity),
	apply_equivs(Depth1,Arity,OldFAtom,FAtom),
	recorded(aleph_dyn,flatten_lits(OldLast),DbRef),
	(CheckOArgs = true -> 
		arg(3,Mode,Out),
		get_vars(FAtom,Out,OVars),
		(in_path(OVars) ->
			add_new_lit(Depth,FAtom,Mode,OldLast,Negated,NewLast);
			NewLast = OldLast) ;
		add_new_lit(Depth,FAtom,Mode,OldLast,Negated,NewLast)),
	erase(DbRef),
	recorda(aleph_dyn,flatten_lits(NewLast),_),
	fail.
flatten_lits(_,_,_,_,_,_,Last1):-
	recorded(aleph_dyn,flatten_lits(Last1),DbRef),
	erase(DbRef).


% flatten_lit(+Lit,+Mode,+FAtom,-IVars,-OVars)
% variabilise Lit as FAtom
%	Mode contains actual mode and 
%	In, Out, Const positions as term-place numbers with types
% 	replace ground terms with integers denoting variables
%	or special terms denoting constants
% 	variable numbers arising from variable splits are disallowed
%	returns Input and Output variable numbers
flatten_lit(Lit,mode(Mode,In,Out,Const),FAtom,IVars,OVars):-
	functor(Mode,_,Arity),
	once(copy_modeterms(Mode,FAtom,Arity)),
	flatten_vars(In,Lit,FAtom,IVars),
	flatten_vars(Out,Lit,FAtom,OVars),
	flatten_consts(Const,Lit,FAtom).

% flatten_vars(+TPList,+Lit,+FAtom,-Vars):-
% FAtom is Lit with terms-places in TPList replaced by variables
flatten_vars([],_,_,[]).
flatten_vars([Pos/Type|Rest],Lit,FAtom,[Var|Vars]):-
	tparg(Pos,Lit,Term),
	recorded(terms,terms(TNo,_,Term,Type),_),
	recorded(vars,vars(Var,TNo,_,_),_),
	not(recorded(vars,copy(Var,_,_),_)),
	tparg(Pos,FAtom,Var),
	flatten_vars(Rest,Lit,FAtom,Vars).

% replace a list of terms at places marked by # in the modes
% with a special term structure denoting a constant
flatten_consts([],_,_).
flatten_consts([Pos/_|Rest],Lit,FAtom):-
	tparg(Pos,Lit,Term),
	tparg(Pos,FAtom,aleph_const(Term)),
	flatten_consts(Rest,Lit,FAtom).

% in_path(+ListOfOutputVars)
% check to avoid generating useless literals in the last i layer
in_path(OVars):-
	recorded(sat,head_ovars(Vars),_), !,
	(Vars=[];OVars=[];intersects(Vars,OVars)).
in_path(_).

% update_equivs(+VariableEquivalences,+IDepth)
% update variable equivalences created at a particular i-depth
% is non-empty only if variable splitting is allowed
update_equivs([],_):- !.
update_equivs(Equivs,Depth):-
	recorded(vars,equivs(Depth,Eq1),DbRef), !,
	erase(DbRef),
	update_equiv_lists(Equivs,Eq1,Eq2),
	recorda(vars,equivs(Depth,Eq2),_).
update_equivs(Equivs,Depth):-
	Depth1 is Depth - 1,
	get_equivs(Depth1,Eq1),
	update_equiv_lists(Equivs,Eq1,Eq2),
	recorda(vars,equivs(Depth,Eq2),_).

update_equiv_lists([],E,E):- !.
update_equiv_lists([Var/E1|Equivs],ESoFar,E):-
	aleph_delete(Var/E2,ESoFar,ELeft), !,
	update_list(E1,E2,E3),
	update_equiv_lists(Equivs,[Var/E3|ELeft],E).
update_equiv_lists([Equiv|Equivs],ESoFar,E):-
	update_equiv_lists(Equivs,[Equiv|ESoFar],E).

% get variable equivalences at a particular depth
% recursively descend to greatest depth below this for which equivs exist
% also returns the database reference of entry
get_equivs(Depth,[]):-
	Depth < 0, !.
get_equivs(Depth,Equivs):-
	recorded(vars,equivs(Depth,Equivs),_), !.
get_equivs(Depth,E):-
	Depth1 is Depth - 1,
	get_equivs(Depth1,E).

% apply equivalences inherited from Depth to a flattened literal
% if no variable splitting, then succeeds only once
apply_equivs(Depth,Arity,Old,New):-
	get_equivs(Depth,Equivs),
	rename(Arity,Equivs,[],Old,New).

% rename args using list of Var/Equivalences
rename(_,[],_,L,L):- !.
rename(0,_,_,_,_):- !.
rename(Pos,Equivs,Subst0,Old,New):-
        arg(Pos,Old,OldVar),
        aleph_member(OldVar/Equiv,Equivs), !,
        aleph_member(NewVar,Equiv),
        arg(Pos,New,NewVar),
        Pos1 is Pos - 1,
        rename(Pos1,Equivs,[OldVar/NewVar|Subst0],Old,New).
rename(Pos,Equivs,Subst0,Old,New):-
        arg(Pos,Old,OldVar),
        (aleph_member(OldVar/NewVar,Subst0) ->
                arg(Pos,New,NewVar);
                arg(Pos,New,OldVar)),
        Pos1 is Pos - 1,
        rename(Pos1,Equivs,Subst0,Old,New).


% add a new literal to lits database
% performs variable splitting if splitvars is set to true
add_new_lit(Depth,FAtom,Mode,OldLast,Negated,NewLast):-
	arg(1,Mode,M),
	functor(FAtom,Name,Arity),
	functor(SplitAtom,Name,Arity),
	once(copy_modeterms(M,SplitAtom,Arity)),
	arg(2,Mode,In), arg(3,Mode,Out), arg(4,Mode,Const),
        split_vars(Depth,FAtom,In,Out,Const,SplitAtom,IVars,OVars,Equivs),
        update_equivs(Equivs,Depth),
        add_lit(OldLast,Negated,SplitAtom,In,Out,IVars,OVars,LitNum),
        insert_eqs(Equivs,Depth,LitNum,NewLast), !.

% modify the literal database: check if performing lazy evaluation
% of bottom clause, and update input and output terms in literal
add_lit(Last,Negated,FAtom,I,O,_,_,Last):-
	(recorded(aleph,set(lazy_bottom,true),_);
		recorded(aleph,set(construct_bottom,false),_)),
	(Negated = true -> Lit = not(FAtom); Lit = FAtom),
	recorded(lits,lit_info(_,0,Lit,I,O,_),_), !.
add_lit(Last,Negated,FAtom,In,Out,IVars,OVars,LitNum):-
	LitNum is Last + 1,
	update_iterms(LitNum,IVars),
	update_oterms(LitNum,OVars,[],Dependents),
	add_litinfo(LitNum,Negated,FAtom,In,Out,Dependents),
	recordz(ivars,ivars(LitNum,IVars),_),
	recordz(ovars,ovars(LitNum,OVars),_), !.


% update lits database after checking that the atom does not exist
% used during updates of lit database by lazy evaluation
update_lit(LitNum,true,FAtom,I,O,D):-
	recorded(lits,lit_info(LitNum,0,not(FAtom),I,O,D),_), !.
update_lit(LitNum,false,FAtom,I,O,D):-
	recorded(lits,lit_info(LitNum,0,FAtom,I,O,D),_), !.
update_lit(LitNum,Negated,FAtom,I,O,D):-
	gen_lit(LitNum),
	add_litinfo(LitNum,Negated,FAtom,I,O,D), 
	get_vars(FAtom,I,IVars),
	get_vars(FAtom,O,OVars),
	recordz(ivars,ivars(LitNum,IVars),_),
	recordz(ovars,ovars(LitNum,OVars),_), !.

% add a literal to lits database without checking
add_litinfo(LitNum,true,FAtom,I,O,D):-
	!,
	recordz(lits,lit_info(LitNum,0,not(FAtom),I,O,D),_).
add_litinfo(LitNum,_,FAtom,I,O,D):-
	recordz(lits,lit_info(LitNum,0,FAtom,I,O,D),_).
	
% update database with input terms of literal
update_iterms(_,[]).
update_iterms(LitNum,[VarNum|Vars]):-
	recorded(vars,vars(VarNum,TNo,I,O),DbRef),
	erase(DbRef),
	update(I,LitNum,NewI),
	recorda(vars,vars(VarNum,TNo,NewI,O),_),
	update_dependents(LitNum,O),
	update_iterms(LitNum,Vars).

% update database with output terms of literal
% return list of dependent literals
update_oterms(_,[],Dependents,Dependents).
update_oterms(LitNum,[VarNum|Vars],DSoFar,Dependents):-
	recorded(vars,vars(VarNum,TNo,I,O),DbRef),
	erase(DbRef),
	update(O,LitNum,NewO),
	recorda(vars,vars(VarNum,TNo,I,NewO),_),
	update_list(I,DSoFar,D1),
	update_oterms(LitNum,Vars,D1,Dependents).

% update Dependent list of literals with LitNum
update_dependents(_,[]).
update_dependents(LitNum,[Lit|Lits]):-
	recorded(lits,lit_info(Lit,Depth,Atom,ITerms,OTerms,Dependents),DbRef),
	erase(DbRef),
	update(Dependents,LitNum,NewD),
	recorda(lits,lit_info(Lit,Depth,Atom,ITerms,OTerms,NewD),_),
	update_dependents(LitNum,Lits).

% update dependents of head with literals that are simply generators
% 	that is, literals that require no input args
update_generators:-
	findall(L,(recorded(lits,lit_info(L,_,_,[],_,_),_),L>1),GList),
	GList \= [], !,
	recorded(lits,lit_info(1,Depth,Lit,I,O,D),DbRef),
	erase(DbRef),
	aleph_append(D,GList,D1),
	recorda(lits,lit_info(1,Depth,Lit,I,O,D1),_).
update_generators.

% recursively mark literals with minimum depth to bind output vars in head
mark_lits([],_,_).
mark_lits(Lits,OldVars,Depth):-
	mark_lits(Lits,Depth,true,[],Predecessors,OldVars,NewVars),
	delete_list(Lits,Predecessors,P1),
	Depth1 is Depth + 1,
	mark_lits(P1,NewVars,Depth1).

mark_lits([],_,_,P,P,V,V).
mark_lits([Lit|Lits],Depth,GetPreds,PSoFar,P,VSoFar,V):-
	recorded(aleph_dyn,marked(Lit/Depth0),DbRef), !,
	(Depth < Depth0 ->
		erase(DbRef),
		mark_lit(Lit,Depth,GetPreds,VSoFar,P1,V2),
		update_list(P1,PSoFar,P2),
		mark_lits(Lits,Depth,GetPreds,P2,P,V2,V);
		mark_lits(Lits,Depth,GetPreds,PSoFar,P,VSoFar,V)).
mark_lits([Lit|Lits],Depth,GetPreds,PSoFar,P,VSoFar,V):-
	mark_lit(Lit,Depth,GetPreds,VSoFar,P1,V2), !,
	update_list(P1,PSoFar,P2),
	mark_lits(Lits,Depth,GetPreds,P2,P,V2,V).
mark_lits([_|Lits],Depth,GetPreds,PSoFar,P,VSoFar,V):-
	mark_lits(Lits,Depth,GetPreds,PSoFar,P,VSoFar,V).

mark_lit(Lit,Depth,GetPreds,VSoFar,P1,V1):-
	recorded(lits,lit_info(Lit,_,Atom,I,O,D),DbRef),
	erase(DbRef),
	recorda(aleph_dyn,marked(Lit/Depth),_),
	recorda(lits,lit_info(Lit,Depth,Atom,I,O,D),_),
	(GetPreds = false ->
		P1 = [],
		V1 = VSoFar;
		get_vars(Atom,O,OVars),
		update_list(OVars,VSoFar,V1),
		get_predicates(D,V1,D1),
		mark_lits(D1,Depth,false,[],_,VSoFar,_),
		get_vars(Atom,I,IVars),
		get_predecessors(IVars,[],P1)).

% mark lits that produce outputs that are not used by any other literal
mark_floating_lits(Lit,Last):-
	Lit > Last, !.
mark_floating_lits(Lit,Last):-
	recorded(lits,lit_info(Lit,_,_,_,O,D),_),
	O \= [],
	(D = []; D = [Lit]), !,
	recorda(aleph_dyn,marked(Lit/0),_),
	Lit1 is Lit + 1,
	mark_floating_lits(Lit1,Last).
mark_floating_lits(Lit,Last):-
	Lit1 is Lit + 1,
	mark_floating_lits(Lit1,Last).
	
% mark lits in bottom clause that are specified redundant by user
% requires definition of redundant/2 that have distinguished first arg ``bottom''
mark_redundant_lits(Lit,Last):-
	Lit > Last, !.
mark_redundant_lits(Lit,Last):-
	recorded(lits,lit_info(Lit,_,Atom,_,_,_),_),
	redundant(bottom,Atom), !,
	recorda(aleph_dyn,marked(Lit/0),_),
	Lit1 is Lit + 1,
	mark_redundant_lits(Lit1,Last).
mark_redundant_lits(Lit,Last):-
	Lit1 is Lit + 1,
	mark_redundant_lits(Lit1,Last).

% get literals that are linked and do not link to any others (ie predicates)
get_predicates([],_,[]).
get_predicates([Lit|Lits],Vars,[Lit|T]):-
	recorded(lits,lit_info(Lit,_,Atom,I,_,[]),_), 
	get_vars(Atom,I,IVars),
	aleph_subset1(IVars,Vars), !,
	get_predicates(Lits,Vars,T).
get_predicates([_|Lits],Vars,T):-
	get_predicates(Lits,Vars,T).

get_predecessors([],P,P).
get_predecessors([Var|Vars],PSoFar,P):-
	recorded(vars,vars(Var,_,_,O),_),
	update_list(O,PSoFar,P1),
	get_predecessors(Vars,P1,P).

% removal of literals that are repeated because of mode differences
rm_moderepeats(_,_):-
	recorded(lits,lit_info(Lit1,_,Pred1,_,_,_),_),
	recorded(lits,lit_info(Lit2,_,Pred1,_,_,_),DbRef),
	Lit1 > 1, Lit2 > Lit1,
	erase(DbRef),
	recorda(aleph_dyn,marked(Lit2/0),_),
	fail.
rm_moderepeats(Last,N):-
	recorded(aleph_dyn,marked(_),_), !,
	get_marked(1,Last,Lits),
	length(Lits,N),
	p1_message('repeated literals'), p_message(N/Last),
	remove_lits(Lits).
rm_moderepeats(_,0).
	
% removal of symmetric literals
rm_symmetric(_,_):-
	recorded(aleph,set(check_symmetry,true),_),
	recorded(lits,lit_info(Lit1,_,Pred1,[I1|T1],_,_),_),
	is_symmetric(Pred1,Name,Arity),
	get_vars(Pred1,[I1|T1],S1),
	recorded(lits,lit_info(Lit2,_,Pred2,[I2|T2],_,_),DbRef),
	not(Lit1=Lit2),
	is_symmetric(Pred2,Name,Arity),
	get_vars(Pred2,[I2|T2],S2),
	equal_set(S1,S2),
	recorda(aleph_dyn,marked(Lit2/0),_),
	erase(DbRef),
	fail.
rm_symmetric(Last,N):-
	recorded(aleph_dyn,marked(_),_), !,
	get_marked(1,Last,Lits),
	length(Lits,N),
	p1_message('symmetric literals'), p_message(N/Last),
	remove_lits(Lits).
rm_symmetric(_,0).

is_symmetric(not(Pred),not(Name),Arity):-
	!,
	functor(Pred,Name,Arity),
	recorded(aleph,symmetric(Name/Arity),_).
is_symmetric(Pred,Name,Arity):-
	functor(Pred,Name,Arity),
	recorded(aleph,symmetric(Name/Arity),_).
	
% removal of literals that are repeated because of commutativity
rm_commutative(_,_):-
	recorded(aleph,commutative(Name/Arity),_),
	p1_message('checking commutative literals'), p_message(Name/Arity),
	functor(Pred,Name,Arity), functor(Pred1,Name,Arity),
	recorded(lits,lit_info(Lit1,_,Pred,[I1|T1],_,_),_),
	get_vars(Pred,[I1|T1],S1),
	recorded(lits,lit_info(Lit2,_,Pred1,[I2|T2],_,_),DbRef),
	not(Lit1=Lit2),
	get_vars(Pred1,[I2|T2],S2),
	equal_set(S1,S2),
	recorda(aleph_dyn,marked(Lit2/0),_),
	erase(DbRef),
	fail.
rm_commutative(Last,N):-
	recorded(aleph_dyn,marked(_),_), !,
	get_marked(1,Last,Lits),
	length(Lits,N),
	p1_message('commutative literals'), p_message(N/Last),
	remove_lits(Lits).
rm_commutative(_,0).

% recursive marking of literals that do not contribute to establishing
% variable chains to output vars in the head
% or produce outputs that are not used by any literal
% controlled by setting flag check_useless
rm_uselesslits(_,0):-
	setting(check_useless,false), !.
rm_uselesslits(Last,N):-
	recorded(sat,head_ovars(OVars),_),
	OVars \= [], !,
	get_predecessors(OVars,[],P),
	recorded(sat,head_ivars(IVars),_),
	mark_lits(P,IVars,0),
	get_unmarked(1,Last,Lits),
	length(Lits,N),
	p1_message('useless literals'), p_message(N/Last),
	remove_lits(Lits).
rm_uselesslits(_,0).

% call user-defined predicate redundant/2 to remove redundant
% literals from bottom clause. Redundancy checking only done on request
rm_redundant(_,0):-
	setting(check_redundant,false), !.
rm_redundant(Last,N):-
	mark_redundant_lits(1,Last),
	get_marked(1,Last,Lits),
	length(Lits,N),
	p1_message('redundant literals'), p_message(N/Last),
	remove_lits(Lits).

% get a list of unmarked literals
get_unmarked(Lit,Last,[]):-
	Lit > Last, !.
get_unmarked(Lit,Last,Lits):-
	recorded(aleph_dyn,marked(Lit/_),DbRef), !,
	erase(DbRef),
	Next is Lit + 1,
	get_unmarked(Next,Last,Lits).
get_unmarked(Lit,Last,[Lit|Lits]):-
	recorded(lits,lit_info(Lit,_,_,_,_,_),DbRef), !,
	erase(DbRef),
	Next is Lit + 1,
	get_unmarked(Next,Last,Lits).
get_unmarked(Lit,Last,Lits):-
	Next is Lit + 1,
	get_unmarked(Next,Last,Lits).

% get a list of marked literals
get_marked(Lit,Last,[]):-
	Lit > Last, !.
get_marked(Lit,Last,[Lit|Lits]):-
	recorded(aleph_dyn,marked(Lit/_),DbRef), !,
	erase(DbRef),
	(recorded(lits,lit_info(Lit,_,_,_,_,_),DbRef1)->
		erase(DbRef1);
		true),
	Next is Lit + 1,
	get_marked(Next,Last,Lits).
get_marked(Lit,Last,Lits):-
	Next is Lit + 1,
	get_marked(Next,Last,Lits).

% update descendent lists of literals by removing useless literals
remove_lits(L):-
	recorded(lits,lit_info(Lit,Depth,A,I,O,D),DbRef),
	erase(DbRef),
	delete_list(L,D,D1),
	recorda(lits,lit_info(Lit,Depth,A,I,O,D1),_),
	fail.
remove_lits(_).

% generate a new literal at depth Depth: forced backtracking will give all lits
gen_layer(Name/Arity,Depth):-
	(Name/Arity = not/1 ->
		recorded(aleph,modeb(NSucc,not(Mode)),_),
		functor(Mode,Name,Arity),
		functor(Lit1,Name,Arity),
		once(copy_modeterms(Mode,Lit1,Arity)),
		Lit = not(Lit1);
		functor(Mode,Name,Arity),
		functor(Lit,Name,Arity),
		recorded(aleph,modeb(NSucc,Mode),_),
		once(copy_modeterms(Mode,Lit,Arity))),
	split_args(Mode,Mode,Input,Output,Constants),
	(Input = [] -> Call1 = true, Call2 = true;
		aleph_delete(Arg/Type,Input,OtherInputs),
		Depth1 is Depth - 1,
		construct_incall(Lit,Depth1,[Arg/Type],Call1),
		construct_call(Lit,Depth,OtherInputs,Call2)),
	Call1,
	Call2,
	get_successes(Lit,NSucc,mode(Mode,Input,Output,Constants)),
	fail.
gen_layer(_,_).


get_successes(Literal,1,M):-
	depth_bound_call(Literal), 
	update_atoms(Literal,M), !.
get_successes(Literal,*,M):-
	depth_bound_call(Literal), 
	update_atoms(Literal,M).
get_successes(Literal,N,M):-
	integer(N),
	N > 1,
	reset_succ,
	get_nsuccesses(Literal,N,M).

% get at most N matches for a literal
get_nsuccesses(Literal,N,M):-
	depth_bound_call(Literal), 
	recorded(aleph_dyn,last_success(Succ0),DbRef),
	erase(DbRef),
	Succ0 < N,
	Succ1 is Succ0 + 1,
	update_atoms(Literal,M),
	recorda(aleph_dyn,last_success(Succ1),_),
	(Succ1 >= N -> !; true).

update_atoms(Atom,M):-
	recorded(atoms,atom(Atom,M),_), !.
update_atoms(Atom,M):-
	recorda(atoms,atom(Atom,M),_).

% call with input term that is an ouput of a previous literal
construct_incall(_,_,[],true):- !.
construct_incall(not(Lit),Depth,Args,Call):-
	!,
	construct_incall(Lit,Depth,Args,Call).
construct_incall(Lit,Depth,[Pos/Type],Call):-
	!,
	Call = legal_term(exact,Depth,Type,Term),
	tparg(Pos,Lit,Term).
construct_incall(Lit,Depth,[Pos/Type|Args],(Call,Calls)):-
	tparg(Pos,Lit,Term),
	Call = legal_term(exact,Depth,Type,Term),
	(var(Depth)-> construct_incall(Lit,_,Args,Calls);
		construct_incall(Lit,Depth,Args,Calls)).

construct_call(_,_,[],true):- !.
construct_call(not(Lit),Depth,Args,Call):-
	!,
	construct_call(Lit,Depth,Args,Call).
construct_call(Lit,Depth,[Pos/Type],Call):-
	!,
	Call = legal_term(upper,Depth,Type,Term),
	tparg(Pos,Lit,Term).
construct_call(Lit,Depth,[Pos/Type|Args],(Call,Calls)):-
	tparg(Pos,Lit,Term),
	Call = legal_term(upper,Depth,Type,Term),
	construct_call(Lit,Depth,Args,Calls).

% generator of legal terms seen so far
legal_term(exact,Depth,Type,Term):-
	recorded(terms,terms(TNo,Depth,Term,Type),_),
	once(recorded(vars,vars(_,TNo,_,[_|_]),_)).
% legal_term(exact,Depth,Type,Term):-
	% recorded(vars,copy(NewVar,OldVar,Depth),_),
	% once(recorded(vars,vars(NewVar,TNo,_,_),_)),
	% recorded(terms,terms(TNo,_,Term,Type),_).
legal_term(upper,Depth,Type,Term):-
	recorded(terms,terms(TNo,Depth1,Term,Type),_),
	Depth1 \= unknown,
	Depth1 < Depth,
	once(recorded(vars,vars(_,TNo,_,[_|_]),_)).
% legal_term(upper,Depth,Type,Term):-
	% recorded(vars,copy(NewVar,OldVar,Depth),_),
	% once(recorded(vars,vars(NewVar,TNo,_,_),_)),
	% recorded(terms,terms(TNo,Depth1,Term,Type),_),
	% Depth1 \= unknown.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% V A R I A B L E  -- S P L I T T I N G


split_vars(Depth,FAtom,I,O,C,SplitAtom,IVars,OVars,Equivs):-
	setting(splitvars,true), !,
        get_args(FAtom,I,[],IVarList),
        get_args(FAtom,O,[],OVarList),
	get_var_equivs(Depth,IVarList,OVarList,IVars,OVars0,Equivs0),
	(Equivs0 = [] ->
		OVars = OVars0, SplitAtom = FAtom, Equivs = Equivs0;
		functor(FAtom,Name,Arity),
		functor(SplitAtom,Name,Arity),
		copy_args(FAtom,SplitAtom,I),
		copy_args(FAtom,SplitAtom,C),
		rename_ovars(O,Depth,FAtom,SplitAtom,Equivs0,Equivs),
		get_argterms(SplitAtom,O,[],OVars)).
	% write('splitting: '), write(FAtom), write(' to: '), write(SplitAtom), nl.
split_vars(_,FAtom,I,O,_,FAtom,IVars,OVars,[]):-
	get_vars(FAtom,I,IVars),
	get_vars(FAtom,O,OVars).

% get equivalent classes of variables from co-references 
get_var_equivs(Depth,IVarList,OVarList,IVars,OVars,Equivs):-
	sort(IVarList,IVars),
	sort(OVarList,OVars),
	(Depth = 0 ->
		intersect1(IVars,OVarList,IOCoRefs,_),
		get_repeats(IVarList,IOCoRefs,ICoRefs);
		intersect1(IVars,OVarList,ICoRefs,_)),
	get_repeats(OVarList,ICoRefs,CoRefs),
	add_equivalences(CoRefs,Depth,Equivs).

add_equivalences([],_,[]).
add_equivalences([Var|Vars],Depth,[Var/E|Rest]):-
	% (Depth = 0 -> E = []; E = [Var]),
	E = [Var],
	add_equivalences(Vars,Depth,Rest).


get_repeats([],L,L).
get_repeats([Var|Vars],Ref1,L):-
	aleph_member1(Var,Vars), !,
	update(Ref1,Var,Ref2),
	get_repeats(Vars,Ref2,L).
get_repeats([_|Vars],Ref,L):-
	get_repeats(Vars,Ref,L).

% rename all output vars that are co-references
% updates vars database and return equivalent class of variables
rename_ovars([],_,_,_,L,L).
rename_ovars([ArgNo|Args],Depth,Old,New,CoRefs,Equivalences):-
	(ArgNo = Pos/_ -> true; Pos = ArgNo),
	tparg(Pos,Old,OldVar),
	aleph_delete(OldVar/Equiv,CoRefs,Rest), !,
	copy_var(OldVar,NewVar,Depth),
	tparg(Pos,New,NewVar),
	rename_ovars(Args,Depth,Old,New,[OldVar/[NewVar|Equiv]|Rest],Equivalences).
rename_ovars([ArgNo|Args],Depth,Old,New,CoRefs,Equivalences):-
	(ArgNo = Pos/_ -> true; Pos = ArgNo),
	tparg(Pos,Old,OldVar),
	tparg(Pos,New,OldVar),
	rename_ovars(Args,Depth,Old,New,CoRefs,Equivalences).

% create new  equalities to  allow co-references to re-appear in search
insert_eqs([],_,L,L).
insert_eqs([OldVar/Equivs|Rest],Depth,Last,NewLast):-
	recorded(vars,vars(OldVar,TNo,_,_),_),
	recorded(terms,terms(TNo,_,_,Type),_),
	add_eqs(Equivs,Depth,Type,Last,Last1),
	insert_eqs(Rest,Depth,Last1,NewLast).

add_eqs([],_,_,L,L).
add_eqs([V1|Rest],Depth,Type,Last,NewLast):-
	add_eqs(Rest,Depth,V1,Type,Last,Last1),
	add_eqs(Rest,Depth,Type,Last1,NewLast).

add_eqs([],_,_,_,L,L).
add_eqs([Var2|Rest],Depth,Var1,Type,Last,NewLast):-
	(Depth = 0 -> 
		add_lit(Last,false,(Var1=Var2),[1/Type],[2/Type],[Var1],[Var2],Last1);
		add_lit(Last,false,(Var1=Var2),[1/Type,2/Type],[],[Var1,Var2],[],Last1)),
	add_eqs(Rest,Depth,Var1,Type,Last1,NewLast).
	


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% utilities for updating mappings between terms and variables

% integrate terms specified by a list of arguments
% integrating a term means:
%	updating 2 databases: terms and vars
%	terms contains the term along with a term-id
%	vars contains a var-id <-> term-id mapping
% var and term-ids are integers
integrate_args(_,_,[]).
integrate_args(Depth,Literal,[Pos/Type|T]):-
        tparg(Pos,Literal,Term),
        integrate_term(Depth,Term/Type),
        (recorded(terms,terms(TNo,Depth,Term,unknown),DbRef)->
                        erase(DbRef),
                        recorda(terms,terms(TNo,Depth,Term,Type),_);
                        true),
        integrate_args(Depth,Literal,T).


% integrate a term
integrate_term(Depth,Term/Type):-
        recorded(terms,terms(TNo,Depth,Term,Type),_),
        recorded(vars,vars(_,TNo,_,[_|_]),_), !.
integrate_term(Depth,Term/Type):-
        recorded(terms,terms(TNo,Depth1,Term,Type),DbRef),
        (Type = unknown ; recorded(vars,vars(_,TNo,_,[]),_)), !,
	(Depth1 = unknown ->
        	erase(DbRef),
		recorda(terms,terms(TNo,Depth,Term,Type),_);
                true).
integrate_term(_,Term/Type):-
        recorded(terms,terms(_,_,Term,Type),_),
        not(Type = unknown),
        !.
integrate_term(Depth,Term/Type):-
	recorded(sat,last_term(Num),DbRef),
	erase(DbRef),
	recorded(sat,last_var(Var0),DbRef1),
	erase(DbRef1),
	TNo is Num + 1,
	Var is Var0 + 1,
	recorda(sat,last_term(TNo),_),
	recorda(sat,last_var(Var),_),
	recorda(vars,vars(Var,TNo,[],[]),_),
	recorda(terms,terms(TNo,Depth,Term,Type),_).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% split_args(+Lit,?Mode,-Input,-Output,-Constants)
%       return term-places and types of +,-, and # args in Lit
%       by finding a matching mode declaration if Mode is given
%       otherwise first mode that matches is used
split_args(Lit,Mode,Input,Output,Constants):-
        functor(Lit,Psym,Arity),
        functor(Mode,Psym,Arity),
        functor(Template,Psym,Arity),
        recorded(aleph,mode(_,Mode),_),
	copy_modeterms(Mode,Template,Arity),
	Template = Lit,
	tp(Mode,TPList),
	split_tp(TPList,Input,Output,Constants).

% split_tp(+TPList,-Input,-Output,-Constants)
%	split term-place/type list into +,-,#
split_tp([],[],[],[]).
split_tp([(+Type)/Place|TP],[Place/Type|Input],Output,Constants):-
	!,
	split_tp(TP,Input,Output,Constants).
split_tp([(-Type)/Place|TP],Input,[Place/Type|Output],Constants):-
	!,
	split_tp(TP,Input,Output,Constants).
split_tp([(#Type)/Place|TP],Input,Output,[Place/Type|Constants]):-
	!,
	split_tp(TP,Input,Output,Constants).
split_tp([_|TP],Input,Output,Constants):-
	split_tp(TP,Input,Output,Constants).

% tp(+Literal,-TPList)
%	return terms and places in Literal
tp(Literal,TPList):-
	functor(Literal,_,Arity),
	tp_list(Literal,Arity,[],[],TPList).

tp_list(_,0,_,L,L):- !.
tp_list(Term,Pos,PlaceList,TpSoFar,TpList):-
	arg(Pos,Term,Arg),
	aleph_append([Pos],PlaceList,Places),
	unwrap_term(Arg,Places,[Arg/Places|TpSoFar],L1),
	Pos1 is Pos - 1,
	tp_list(Term,Pos1,PlaceList,L1,TpList).

unwrap_term(Term,_,L,L):-
	var(Term), !.
unwrap_term(Term,Place,TpSoFar,TpList):-
	functor(Term,_,Arity),
	tp_list(Term,Arity,Place,TpSoFar,TpList).

get_determs(PSym/Arity,L):-
	findall(Pred,recorded(aleph,determination(PSym/Arity,Pred),_),L).

get_modes(PSym/Arity,L):-
	functor(Lit,PSym,Arity),
	findall(Lit,recorded(aleph,mode(_,Lit),_),L).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% S E A R C H

% basic search engine for single clause search
search(S,Nodes):-
	arg(36,S,Time),
	Time \= inf, 
	SearchTime is integer(Time),
	SearchTime > 0, !,
	alarm(SearchTime,throw(searchlimit),_),
	catch(graphsearch(S,_),searchlimit,p_message('Time limit reached')),
	recorded(search,current(_,Nodes,_),_),
	alarm(0,_,_).
search(S,Nodes):-
	graphsearch(S,Nodes).

% basic search engine for theory-based search
tsearch(S,Nodes):-
        arg(36,S,Time),
        Time \= inf,
        SearchTime is integer(Time),
        SearchTime > 0, !,
        alarm(SearchTime,throw(searchlimit),_),
        catch(theorysearch(S,Nodes),searchlimit,p_message('Time limit reached')),
        alarm(0,_,_).
tsearch(S,Nodes):-
        theorysearch(S,Nodes).

graphsearch(S,Nodes):-
	next_node(_), !,
	arg(23,S,LazyPreds),
        arg(3,S,RefineOp),
        repeat,
	next_node(NodeRef),
        once(recorded(search,current(LastE,Last,BestSoFar),DbRef1)),
        expand(RefineOp,S,NodeRef,Node,Path,MinLength,Succ,PosCover,NegCover,OVars,
		PrefixClause,PrefixTV,PrefixLength),
        ((LazyPreds = []; RefineOp = true)  -> Succ1 = Succ;
		lazy_evaluate(Succ,LazyPreds,Path,PosCover,NegCover,Succ1)),
	NextE is LastE + 1,
        get_gains(S,Last,BestSoFar,Path,PrefixClause,PrefixTV,PrefixLength,
                MinLength,Succ1,PosCover,NegCover,OVars,NextE,Last0,NextBest0),
	(RefineOp = true -> Last1 = Last0, NextBest = NextBest0;
        	get_sibgains(S,Node,Last0,NextBest0,Path,PrefixClause,
			PrefixTV,PrefixLength,MinLength,PosCover,NegCover,
			OVars,NextE,Last1,NextBest)),
        recorda(search,current(NextE,Last1,NextBest),_),
        NextL is Last + 1,
        recorda(search,expansion(NextE,Node,NextL,Last1),_),
        (discontinue_search(S,NextBest,Last1) ->
                recorded(search,current(_,Nodes,_),_);
                erase(DbRef1),
                prune_open(S,BestSoFar,NextBest),
                get_nextbest(S,Next),
		Next = none,
		recorded(search,current(_,Nodes,_),_)),
	!.
graphsearch(_,Nodes):-
	recorded(search,current(_,Nodes,_),_).

theorysearch(S,Nodes):-
        next_node(_), !,
        recorded(aleph,atoms(pos,Pos),_),
        recorded(aleph,atoms(neg,Neg),_),
        interval_count(Pos,P),
        interval_count(Neg,N),
        repeat,
        next_node(NodeRef),
        instance(NodeRef,node(_,Theory,_,_,_,_,_,_)),
        once(recorded(search,current(_,Last,BestSoFar),DbRef1)),
        get_theory_gain(S,Last,BestSoFar,Theory,Pos,Neg,P,N,NextBest,Last1),
        erase(DbRef1),
        recorda(search,current(0,Last1,NextBest),_),
        (discontinue_search(S,NextBest,Last1) ->
                recorded(search,current(_,Nodes,_),_);
                prune_open(S,BestSoFar,NextBest),
                get_nextbest(S,Next),
                Next = none,
                recorded(search,current(_,Nodes,_),_)),
	 !.
theorysearch(_,Nodes):-
        recorded(search,current(_,Nodes,_),_).

next_node(NodeRef):-
	once(recorded(search,nextnode(NodeRef),_)), !.

get_search_settings(S):-
        functor(S,set,39),
	(setting(nodes,MaxNodes)-> arg(1,S,MaxNodes); arg(1,S,0)),
	(setting(explore,Explore)-> arg(2,S,Explore); arg(2,S,false)),
	(setting(refineop,RefineOp)-> arg(3,S,RefineOp); arg(3,S,false)),
	(setting(search,Search)->true; Search=bf),
	(setting(evalfn,EvalFn)->true; EvalFn=coverage),
	arg(4,S,Search/EvalFn),
	(setting(greedy,Greedy)-> arg(5,S,Greedy); arg(5,S,false)),
	(setting(verbosity,Verbose)-> arg(6,S,Verbose); arg(6,S,1)),
	(setting(clauselength,CLength)-> arg(7,S,CLength); arg(7,S,4)),
	(setting(caching,Cache)-> arg(8,S,Cache); arg(8,S,false)),
	(setting(prune_defs,Prune)-> arg(9,S,Prune); arg(9,S,false)),
	(setting(lazy_on_cost,LCost)-> arg(10,S,LCost); arg(10,S,false)),
	(setting(lazy_on_contradiction,LContra)-> arg(11,S,LContra); arg(11,S,false)),
	(setting(lazy_negs,LNegs)-> arg(12,S,LNegs); arg(12,S,false)),
	(setting(minpos,MinPos)-> arg(13,S,MinPos); arg(13,S,1)),
	(setting(depth,Depth)-> arg(14,S,Depth); arg(14,S,10)),
	(setting(cache_clauselength,CCLim) -> arg(15,S,CCLim); arg(15,S,3)),
        (recorded(aleph,size(pos,PSize),_)-> arg(16,S,PSize); arg(16,S,0)),
	(setting(noise,Noise)-> arg(17,S,Noise); arg(17,S,false)),
	(setting(minacc,MinAcc)-> arg(18,S,MinAcc); arg(18,S,false)),
	(setting(computation_rule,CRule)-> arg(19,S,CRule); arg(19,S,false)),
        (recorded(aleph,size(rand,RSize),_)-> arg(20,S,RSize); arg(20,S,0)),
	(setting(lazy_bottom,LBot)-> arg(21,S,LBot); arg(21,S,false)),
	(setting(refine,Refine)-> arg(22,S,Refine); arg(22,S,false)),
	findall(PN/PA,recorded(aleph,lazy_evaluate(PN/PA),_),LazyPreds),
	arg(23,S,LazyPreds),
        (recorded(aleph,size(neg,NSize),_)-> arg(24,S,NSize); arg(24,S,0)),
	(setting(openlist,OSize)-> arg(25,S,OSize); arg(25,S,inf)),
        (setting(check_redundant,RCheck)-> arg(26,S,RCheck); arg(26,S,false)),
        (recorded(sat,set(eq,Eq),_)-> arg(27,S,Eq); arg(27,S,false)),
        (recorded(sat,head_ovars(HOVars),_)-> arg(28,S,HOVars); arg(28,S,HOVars)),
	(setting(prooftime,PTime) -> arg(29,S,PTime); arg(29,S,inf)),
	(setting(construct_bottom,CBott) -> arg(30,S,CBott); arg(30,S,saturation)),
	(get_ovars1(1,ovars,lits,HIVars) ->  arg(31,S,HIVars); arg(31,S,[])),
	(setting(language,Lang) -> arg(32,S,Lang); arg(32,S,false)),
	(setting(splitvars,Split) -> arg(33,S,Split);arg(33,S,false)),
	(setting(proof_strategy,Proof) -> arg(34,S,Proof);arg(34,S,restricted_sld)),
	(setting(portray_search,VSearch) -> arg(35,S,VSearch);arg(35,S,false)),
	(setting(searchtime,Time) -> arg(36,S,Time);arg(36,S,inf)),
	(setting(optimise_clauses,Optim) -> arg(37,S,Optim);arg(37,S,false)),
	(setting(newvars,NewV) -> arg(38,S,NewV);arg(38,S,inf)),
	(setting(rls_type,RlsType) -> arg(39,S,RlsType);arg(39,S,false)).

% stop search from proceeding if certain
% conditions are reached. These are:
%	. minacc and minpos values reached in rrr search
%	. best hypothesis has accuracy 1.0 if evalfn=accuracy
%	. best hypothesis covers all positive examples
discontinue_search(S,[P,N,_,_]/_,_):-
	arg(39,S,RlsType),
	RlsType = rrr, 
	arg(18,S,MinAcc),
	arg(13,S,MinPos),
	Acc is P/(P+N),
	Acc >= MinAcc, 
	P >= MinPos, !.
discontinue_search(S,_,Nodes):-
        arg(1,S,MaxNodes),
        Nodes >= MaxNodes, !,
	p_message('node limit exceeded').
discontinue_search(S,[_,_,_,F|_]/_,_):-
        arg(4,S,_/Evalfn),
	Evalfn = accuracy,
	F = 1.0, !.
discontinue_search(S,Best,_):-
	Best = [P|_]/_,
	arg(16,S,P).

update_max_head_count(N,0):-
	retract_all(aleph_dyn,max_head_count(_)),
	recorda(aleph_dyn,max_head_count(N),_), !.
update_max_head_count(Count,Last):-
	NodeIndex is Last // 1000,
	recorded(NodeIndex,node(Last,LitNum,_,_,PosCover,_,_,_),_), !,
	recorda(aleph_dyn,head_lit(LitNum),_),
	interval_count(PosCover,N),
	Next is Last - 1,
	(N > Count -> update_max_head_count(N,Next);
		update_max_head_count(Count,Next)).
update_max_head_count(Count,Last):-
	Next is Last - 1,
	update_max_head_count(Count,Next).

expand(true,S,DbRef,NodeNum,Path1,Length,[_],PosCover,NegCover,OVars,_,_,_):-
        instance(DbRef,node(NodeNum,_,Path1,Length/_,_,_,OVars,_)),
        erase(DbRef),
        arg(5,S,Greedy),
        (Greedy = true ->
                recorded(aleph,atoms_left(pos,PosCover),_);
                arg(16,S,PSize),
                PosCover = [1-PSize]),
        arg(4,S,_/Evalfn),
	(Evalfn = posonly -> 
                recorded(aleph,atoms_left(rand,NegCover),_);
                arg(24,S,NSize),
                NegCover = [1-NSize]).
expand(false,_,DbRef,NodeNum,Path1,Length,Descendents,PCover,NCover,OVars,C,TV,CL):-
        instance(DbRef,node(NodeNum,LitNum,Path,Length/_,PCover,NCover,OVars,_)),
        aleph_append([LitNum],Path,Path1),
	get_pclause(Path1,[],C,TV,CL,_),
        recorded(lits,lit_info(LitNum,_,_,_,_,Dependents),_),
        intersect1(Dependents,Path1,_,Succ),
        check_parents(Succ,OVars,Descendents,_).

get_ovars([],_,_,V,V).
get_ovars([LitNum|Lits],K1,K2,VarsSoFar,Vars):-
	get_ovars1(LitNum,K1,K2,OVars),
	aleph_append(VarsSoFar,OVars,Vars1),
	get_ovars(Lits,K1,K2,Vars1,Vars).

get_ovars1(LitNum,K1,_,OVars):-
	recorded(K1,ovars(LitNum,OVars),_), !.
get_ovars1(LitNum,_,K2,OVars):-
	recorded(K2,lit_info(LitNum,_,Atom,_,O,_),_),
	get_vars(Atom,O,OVars).


% get set of vars at term-places specified
get_vars(not(Literal),Args,Vars):-
	!,
	get_vars(Literal,Args,Vars).
get_vars(_,[],[]).
get_vars(Literal,[ArgNo|Args],Vars):-
	(ArgNo = Pos/_ -> true; Pos = ArgNo),
	tparg(Pos,Literal,Term),
	get_vars_in_term([Term],TV1),
	get_vars(Literal,Args,TV2),
	update_list(TV2,TV1,Vars).

get_vars_in_term([],[]).
get_vars_in_term([Var|Terms],[Var|TVars]):-
	integer(Var), !,
	get_vars_in_term(Terms,TVars).
get_vars_in_term([Term|Terms],TVars):-
	Term =.. [_|Terms1],
	get_vars_in_term(Terms1,TV1),
	get_vars_in_term(Terms,TV2),
	update_list(TV2,TV1,TVars).

% get terms at term-places specified
% need not be variables
get_argterms(not(Literal),Args,TermsSoFar,Terms):-
        !,
        get_argterms(Literal,Args,TermsSoFar,Terms).
get_argterms(_,[],Terms,Terms).
get_argterms(Literal,[ArgNo|Args],TermsSoFar,Terms):-
	(ArgNo = Pos/_ -> true; Pos = ArgNo),
        tparg(Pos,Literal,Term),
        update(TermsSoFar,Term,T1),
        get_argterms(Literal,Args,T1,Terms).

% get list of terms at arg positions specified
get_args(not(Literal),Args,TermsSoFar,Terms):-
        !,
        get_args(Literal,Args,TermsSoFar,Terms).
get_args(_,[],Terms,Terms).
get_args(Literal,[ArgNo|Args],TermsSoFar,Terms):-
	(ArgNo = Pos/_ -> true; Pos = ArgNo),
        tparg(Pos,Literal,Term),
        get_args(Literal,Args,[Term|TermsSoFar],Terms).



get_ivars([],_,_,V,V).
get_ivars([LitNum|Lits],K1,K2,VarsSoFar,Vars):-
	get_ivars1(LitNum,K1,K2,IVars),
	aleph_append(VarsSoFar,IVars,Vars1),
	get_ivars(Lits,K1,K2,Vars1,Vars).

get_ivars1(LitNum,K1,_,IVars):-
	recorded(K1,ivars(LitNum,IVars),_), !.
get_ivars1(LitNum,_,K2,IVars):-
	recorded(K2,lit_info(LitNum,_,Atom,I,_,_),_),
	get_vars(Atom,I,IVars).

check_parents([],_,[],[]).
check_parents([LitNum|Lits],OutputVars,[LitNum|DLits],Rest):-
	get_ivars1(LitNum,ivars,lits,IVars),
	aleph_subset1(IVars,OutputVars), !,
	check_parents(Lits,OutputVars,DLits,Rest).
check_parents([LitNum|Lits],OutputVars,DLits,[LitNum|Rest]):-
	check_parents(Lits,OutputVars,DLits,Rest), !.


get_gains(S,Last,Best,_,_,_,_,_,_,_,_,_,_,Last,Best):-
        discontinue_search(S,Best,Last), !.
get_gains(_,Last,Best,_,_,_,_,_,[],_,_,_,_,Last,Best):- !.
get_gains(S,Last,Best,Path,C,TV,L,Min,[L1|Succ],Pos,Neg,OVars,E,Last1,NextBest):-
        get_gain(S,upper,Last,Best,Path,C,TV,L,Min,L1,Pos,Neg,OVars,E,Best1,Node1), !,
        get_gains(S,Node1,Best1,Path,C,TV,L,Min,Succ,Pos,Neg,OVars,E,Last1,NextBest).
get_gains(S,Last,BestSoFar,Path,C,TV,L,Min,[_|Succ],Pos,Neg,OVars,E,Last1,NextBest):-
        get_gains(S,Last,BestSoFar,Path,C,TV,L,Min,Succ,Pos,Neg,OVars,E,Last1,NextBest),
        !.

get_sibgains(S,Node,Last,Best,Path,C,TV,L,Min,Pos,Neg,OVars,E,Last1,NextBest):-
        NodeIndex is Node // 1000,
        recorded(NodeIndex,node(Node,LitNum,_,_,_,_,_,OldE),_),
        recorded(search,expansion(OldE,_,_,LastSib),_),
        recorded(lits,lit_info(LitNum,_,_,_,_,Desc),_),
        Node1 is Node + 1,
        arg(31,S,HIVars),
        delete_list(HIVars,OVars,LVars),
        get_sibgain(S,LVars,LitNum,Desc,Node1,LastSib,Last,
                Best,Path,C,TV,L,Min,Pos,Neg,OVars,E,NextBest,Last1), !.

get_sibgain(S,_,_,_,Node,Node1,Last,Best,_,_,_,_,_,_,_,_,_,Best,Last):-
        (Node > Node1;
        discontinue_search(S,Best,Last)), !.
get_sibgain(S,LVars,LitNum,Desc,Node,LastSib,Last,Best,Path,C,TV,L,Min,Pos,Neg,OVars,E,LBest,LNode):-
        arg(23,S,Lazy),
        get_sibpncover(Lazy,Node,Desc,Pos,Neg,Sib1,PC,NC),
        lazy_evaluate([Sib1],Lazy,Path,PC,NC,[Sib]),
        get_ivars1(Sib,ivars,lits,SibIVars),
        (intersects(SibIVars,LVars) -> Flag = upper;
                get_ovars1(Sib,ovars,lits,SibOVars),
                (intersects(SibOVars,LVars) -> Flag = upper; Flag = exact)),
        get_gain(S,Flag,Last,Best,Path,C,TV,L,Min,Sib,PC,NC,OVars,E,Best1,Node1), !,
        NextNode is Node + 1,
        get_sibgain(S,LVars,LitNum,Desc,NextNode,LastSib,Node1,Best1,Path,C,TV,L,
                        Min,Pos,Neg,OVars,E,LBest,LNode), !.
get_sibgain(S,LVars,LitNum,Desc,Node,LastSib,Last,Best,Path,C,TV,L,Min,Pos,Neg,OVars,E,Best1,Node1):-
	NextNode is Node + 1,
        get_sibgain(S,LVars,LitNum,Desc,NextNode,LastSib,Last,Best,Path,C,TV,L,
                        Min,Pos,Neg,OVars,E,Best1,Node1), !.


get_sibgain(S,LVars,LitNum,Node,LastSib,Last,Best,Path,C,TV,L,Min,Pos,Neg,OVars,E,Best1,Node1):-
	NextNode is Node + 1,
	get_sibgain(S,LVars,LitNum,NextNode,LastSib,Last,Best,Path,C,TV,L,Min,Pos,Neg,
			OVars,E,Best1,Node1), !.

get_sibpncover(Lazy,NodeNum,Desc,Pos,Neg,Sib,PC,NC):-
        NodeIndex is NodeNum // 1000,
        recorded(NodeIndex,node(NodeNum,Sib,_,_,Pos1,Neg1,_,_),_),
        recorded(lits,lit_info(Sib,_,Atom,_,_,_),_),
        not(aleph_member1(Sib,Desc)),
        functor(Atom,Name,Arity),
        (member1(Name/Arity,Lazy) ->
                PC = Pos, NC = Neg;
                calc_intersection(Pos,Pos1,PC),
                calc_intersection(Neg,Neg1,NC)).

% in some cases, it is possible to simply use the intersection of
% covers cached. The conditions under which this is possible was developed
% in discussions with James Cussens
calc_intersection(A1/[B1-L1],A2/[B2-L2],A/[B-L]):-
	!,
	intervals_intersection(A1,A2,A),
	B3 is max(B1,B2),
	(intervals_intersects(A1,[B2-L2],X3-_) -> true; X3 = B3),
	(intervals_intersects(A2,[B1-L1],X4-_) -> true; X4 = B3),
	B4 is min(X3,B3),
	B is min(X4,B4),
	L is max(L1,L2).
calc_intersection(A1/_,A2,A):-
	!,
	intervals_intersection(A1,A2,A).
calc_intersection(A1,A2/_,A):-
	!,
	intervals_intersection(A1,A2,A).
calc_intersection(A1,A2,A):-
	intervals_intersection(A1,A2,A).
	

get_gain(S,_,Last,Best,Path,_,_,_,MinLength,_,Pos,Neg,OVars,E,Best1,NewLast):-
        arg(3,S,RefineOp),
        RefineOp = true , !,
	get_refine_gain(S,Last,Best,Path,MinLength,Pos,Neg,OVars,E,Best1,NewLast).
get_gain(S,Flag,Last,Best/Node,Path,C,TV,Len1,MinLen,L1,Pos,Neg,OVars,E,Best1,Last1):-
	arg(26,S,RCheck),
	arg(33,S,SplitVars),
	retract_all(covers),
        get_pclause([L1],TV,Lit1,_,Len2,LastD),
	split_ok(SplitVars,C,Lit1), !,
        extend_clause(C,Lit1,Clause1),
	(RCheck = true ->
		(redundant(Clause1,Lit1) -> fail; true);
		true),
        CLen is Len1 + Len2,
        length_ok(S,MinLen,CLen,LastD,EMin,ELength),
	arg(19,S,CRule),
	(CRule = leftmost_with_delay ->
		reorder_goals(Clause1,Clause);
		Clause = Clause1),
        split_clause(Clause,Head,Body),
        recordz(pclause,pclause(Head,Body),DbRef),
        arg(6,S,Verbosity),
        (Verbosity >= 1 -> pp_dclause(Clause); true),
        get_gain1(S,Flag,DbRef,Clause,CLen,EMin/ELength,Last,Best/Node,
                        Path,L1,Pos,Neg,OVars,E,Best1),
        erase(DbRef),
        Last1 is Last + 1.
get_gain(_,_,Last,Best,_,_,_,_,_,_,_,_,_,_,Best,Last).

get_refine_gain(S,Last,Best/Node,Path,MinLength,Pos,Neg,OVars,E,Best1,NewLast):-
        arg(22,S,RefineType),
	RefineType = rls,
	% arg(30,S,ConstructBottom),
	% ConstructBottom = saturation,	% need prior bottom clause
	refine_prelims(Best/Node,Last),
	rls_refine(clauses,Path,Path1),
	get_refine_gain1(S,Path1,MinLength,Pos,Neg,OVars,E,Best1,NewLast),
	!.
get_refine_gain(S,Last,Best/Node,Path,MinLength,Pos,Neg,OVars,E,Best1,NewLast):-
        arg(22,S,RefineType),
	RefineType \= rls,
	refine_prelims(Best/Node,Last),
	Path = CL-[Example,Type,Ids,Clause],
	arg(30,S,ConstructBottom),
	get_user_refinement(RefineType,Clause,R,Id),
	match_bot(ConstructBottom,R,R1),
	Path1 = CL-[Example,Type,[Id|Ids],R1],
	get_refine_gain1(S,Path1,MinLength,Pos,Neg,OVars,E,Best1,NewLast),
	!.
get_refine_gain(_,_,_,_,_,_,_,_,_,Best,Last):-
	recorded(aleph,best_refinement(Best),DbRef),
	recorded(aleph,last_refinement(Last),DbRef1),
	erase(DbRef),
	erase(DbRef1).

get_theory_gain(S,Last,BestSoFar,T0,Pos,Neg,P,N,Best1,NewLast):-
	refine_prelims(BestSoFar,Last),
	arg(22,S,Refine),
	(Refine = rls -> rls_refine(theories,T0,T1);
		(Refine = mcmc -> mcmc_refine(T0,T1); fail)),
	arg(23,S,LazyPreds),
	(LazyPreds = [] -> Theory = T1;
		lazy_evaluate_theory(T1,LazyPreds,Pos,Neg,Theory)),
	recorded(aleph,best_refinement(OldBest),DbRef1),
	recorded(aleph,last_refinement(OldLast),DbRef2),
        arg(6,S,Verbosity),
        (Verbosity >= 1 ->
                p_message('new refinement'),
                pp_dclauses(Theory);
        true),
	arg(19,S,CRule),
	record_pclauses(Theory,CRule,DbRefs),
	get_theory_gain1(S,DbRefs,Theory,OldLast,OldBest,Pos,Neg,P,N,Best1),
	retract_all(pclause),
	erase(DbRef2),
        NewLast is OldLast + 1,
	recorda(aleph,last_refinement(NewLast),DbRef3),
        erase(DbRef1),
        recorda(aleph,best_refinement(Best1),DbRef4),
	(discontinue_search(S,Best1,NewLast) ->
		erase(DbRef3),
		erase(DbRef4);
		fail),
	!.
get_theory_gain(_,_,_,_,_,_,_,_,Best,Last):-
	recorded(aleph,best_refinement(Best),DbRef),
	recorded(aleph,last_refinement(Last),DbRef1),
	erase(DbRef),
	erase(DbRef1).

refine_prelims(Best,Last):-
        retract_all(aleph,best_refinement(_)),
        retract_all(aleph,last_refinement(_)),
	recorda(aleph,best_refinement(Best),_),
	recorda(aleph,last_refinement(Last),_).


get_refine_gain1(S,Path,MinLength,Pos,Neg,OVars,E,Best1,NewLast):-
        arg(23,S,LazyPreds),
	Path = CL-[Example,Type,Ids,Refine],
	(LazyPreds = [] -> Clause1 = Refine;
		lazy_evaluate_refinement(Refine,LazyPreds,Pos,Neg,Clause1)),
	retract_all(covers),
	arg(19,S,CRule),
	(CRule = leftmost_with_delay ->
		reorder_goals(Clause1,Clause);
		Clause = Clause1),
	Path1 = CL-[Example,Type,Ids,Clause],
	split_clause(Clause,Head,Body),
	nlits(Body,CLength0),
	CLength is CLength0 + 1,
	length_ok(S,MinLength,CLength,0,EMin,ELength),
	recordz(pclause,pclause(Head,Body),DbRef),
	recorded(aleph,best_refinement(OldBest),DbRef1),
	recorded(aleph,last_refinement(OldLast),DbRef2),
        arg(6,S,Verbosity),
        (Verbosity >= 1 ->
		p_message('new refinement'),
		pp_dclause(Clause);
	true),
	once(get_gain1(S,upper,DbRef,Clause,CLength,EMin/ELength,OldLast,OldBest,
		Path1,[],Pos,Neg,OVars,E,Best1)),
	erase(DbRef),
	erase(DbRef2),
	NewLast is OldLast + 1,
	recorda(aleph,last_refinement(NewLast),DbRef3),
	erase(DbRef1),
	recorda(aleph,best_refinement(Best1),DbRef4),
	(discontinue_search(S,Best1,NewLast) ->
		erase(DbRef3),
		erase(DbRef4);
		fail),
	!.
get_theory_gain1(S,_,Theory,Last,Best,Pos,Neg,P,N,Best1):-
        (false -> p_message('constraint violated'),
                Contradiction = true;
                Contradiction = false),
	Contradiction = false,
        Node1 is Last + 1,
	arg(32,S,Lang),
	(Lang = false -> true; theory_lang_ok(Theory,Lang)),
	arg(38,S,NewVars),
	(NewVars = inf -> true; theory_newvars_ok(Theory,NewVars)),
	arg(14,S,Depth),
	arg(29,S,Time),
        prove(Depth/Time,pos,(X:-X),Pos,PCvr,TP),
        prove(Depth/Time,neg,(X:-X),Neg,NCvr,FP),
	arg(4,S,_/Evalfn),
	Correct is TP + (N - FP),
	Incorrect is FP + (P - TP),
	length(Theory,L),
	Label = [Correct,Incorrect,L],
	complete_label(Evalfn,Theory,Label,Label1),
	get_search_keys(heuristic,Label1,SearchKeys),
	arg(6,S,Verbosity),
	(Verbosity >= 1 -> p_message(Correct/Incorrect); true),
	NodeIndex is Node1 // 1000,
	recorda(NodeIndex,node(Node1,Theory,[],0,PCvr,NCvr,[],0),NodeRef),
	update_open_list(SearchKeys,NodeRef,Label1),
	update_best_theory(S,Theory,PCvr,NCvr,Best,Label1/Node1,Best1), !.
get_theory_gain1(_,_,_,_,Best,_,_,_,_,Best).

get_gain1(S,_,DbRef,C,CL,_,Last,Best,Path,_,Pos,Neg,_,E,Best):-
        abandon_branch(S,DbRef), !,
        Node1 is Last + 1,
        arg(7,S,ClauseLength),
	arg(35,S,VSearch),
        (ClauseLength = CL -> true;
                arg(3,S,RefineOp),
                (RefineOp = true  -> true;
			NodeIndex is Node1 // 1000,
                        recorda(NodeIndex,node(Node1,0,Path,0,Pos,Neg,[],E),_))),
	(VSearch = true ->
		recorda(search,bad(Node1),_),
		recorda(search,node(Node1,C),_);
		true),
	arg(22,S,Refine),
	(Refine = probabilistic ->
		Path = _-[_,_,Ids,_],
		inc_beta_counts(Ids,beta); true).
get_gain1(S,_,DbRef,_,_,_,_,Best,Path,_,_,_,_,_,Best):-
        arg(8,S,Caching),
        Caching = true,
        instance(DbRef,pclause(Head,Body)),
        skolemize((Head:-Body),SHead,SBody,0,_),
        recorded(prune_cache,prune([SHead|SBody]),_), !,
        p_message('in prune cache'),
	arg(22,S,Refine),
	(Refine = probabilistic ->
		Path = _-[_,_,Ids,_],
		inc_beta_counts(Ids,beta); true), !.
get_gain1(S,Flag,DbRef,C,CL,EMin/EL,Last,Best/Node,Path,L1,Pos,Neg,OVars,E,Best1):-
        (false -> p_message('constraint violated'),
                Contradiction = true;
                Contradiction = false),
        Node1 is Last + 1,
        arg(8,S,Caching),
        (Caching = true -> arg(15,S,CCLim),
		get_cache_entry(CCLim,C,Entry);
		Entry = false),
	arg(35,S,VSearch),
	(VSearch = true ->
		recorda(search,node(Node1,C),_);
		true),
        arg(3,S,RefineOp),
	(RefineOp = false -> true ;
		arg(22,S,RefineType),
		refinement_ok(RefineType,Entry,RefineOp)),
	instance(DbRef,pclause(Head,Body)),
	arg(32,S,Lang),
	(Lang = false -> true; lang_ok((Head:-Body),Lang)),
	arg(38,S,NewVars),
	(NewVars = inf -> true; newvars_ok((Head:-Body),NewVars)),
	arg(34,S,Proof),
	(Proof = restricted_sld ->
		arg(37,S,Optim),
		(Optim = true -> 
        		optimise((Head:-Body),(Head1:-Body1));
			Head1 = Head,
			Body1 = Body);
		Head1 = Body1),
        prove_examples(S,Flag,Path,Contradiction,Entry,Best,CL,EL,(Head1:-Body1),Pos,Neg,
			PCvr,NCvr,Label),
        arg(4,S,Search/Evalfn),
	complete_label(Evalfn,C,Label,Label1),
	compression_ok(Evalfn,Label1),
        get_search_keys(Search,Label1,SearchKeys),
        arg(6,S,Verbosity),
        (Verbosity >= 1 -> Label = [A,B|_], p_message(A/B); true),
        arg(7,S,ClauseLength),
	(RefineOp = true -> true;
		get_ovars1(L1,ovars,lits,OVars1),
		aleph_append(OVars1,OVars,OVars2)),
        ((ClauseLength=CL, RefineOp \=true) -> true;
		NodeIndex is Node1 // 1000,
		(RefineOp = true ->
                	recorda(NodeIndex,node(Node1,0,Path,EMin/EL,[],
					[],[],E),NodeRef);
                	recorda(NodeIndex,node(Node1,L1,Path,EMin/EL,PCvr,
				NCvr,OVars2,E),NodeRef)),
                	update_open_list(SearchKeys,NodeRef,Label1)),
	(VSearch = true ->
		recorda(search,label(Node1,Label),_);
		true),
        (((RefineOp = true,Contradiction=false); (arg(28,S,HOVars),clause_ok(Contradiction,HOVars,OVars2))) ->
                update_best(S,C,PCvr,NCvr,Best/Node,Label1/Node1,Best1);
                Best1=Best/Node),
	arg(22,S,RefineType),
	(RefineType = probabilistic -> 
		Path = _-[_,_,Ids,_],
		update_probabilistic_refinement(S,Ids,Best/Node,Best1,Label1,
			ClauseLength,CL);
		true), !.
get_gain1(_,_,_,_,_,_,_,Best,_,_,_,_,_,_,Best).


abandon_branch(S,DbRef):-
        arg(9,S,PruneDefined),
        PruneDefined = true,
        instance(DbRef,pclause(Head,Body)),
        prune((Head:-Body)), !,
        arg(6,S,Verbosity),
        (Verbosity >= 1 -> p_message(pruned); true).


clause_ok(false,V1,V2):-
        aleph_subset1(V1,V2).

% check to see if refinement has been produced before
refinement_ok(rls,_,_):- !.
refinement_ok(_,false,_):- !.
refinement_ok(_,_,false):- !.
refinement_ok(_,Entry,true):-
	(check_cache(Entry,pos,_); check_cache(Entry,neg,_)), !,
	p_message('redundant refinement'),
	fail.
refinement_ok(_,_,_).


% specialised redundancy check with equality theory
% used only to check if equalities introduced by splitting vars make
% literal to be added redundant
split_ok(false,_,_):- !.
split_ok(_,Clause,Lit):-
	functor(Lit,Name,_),
	not(Name = '='), 
	copy_term(Clause/Lit,Clause1/Lit1),
	lit_redun(Lit1,Clause1), !,
	p_message('redundant literal'), nl,
	fail.
split_ok(_,_,_).

lit_redun(Lit,(Head:-Body)):-
	!,
	lit_redun(Lit,(Head,Body)).
lit_redun(Lit,(L1,_)):-
	Lit == L1, !.
lit_redun(Lit,(L1,L2)):-
	!,
	execute_equality(L1),
	lit_redun(Lit,L2).
lit_redun(Lit,L):-
	Lit == L.

execute_equality(Lit):-
	functor(Lit,'=',2), !,
	Lit.
execute_equality(_).
	
theory_lang_ok([],_).
theory_lang_ok([_-[_,_,_,Clause]|T],Lang):-
        lang_ok(Clause,Lang),
        theory_lang_ok(T,Lang). 

theory_newvars_ok([],_).
theory_newvars_ok([_-[_,_,_,Clause]|T],NewV):-
        newvars_ok(Clause,NewV),
        theory_newvars_ok(T,NewV). 

lang_ok((Head:-Body),N):-
	!,
	(lang_ok(Head,Body,N) -> true;
		p_message('outside language bound'),
		fail).

lang_ok(Head,Body,N):-
	get_psyms((Head,Body),PSymList),
	lang_ok1(PSymList,N).

newvars_ok((Head:-Body),N):-
	!,
	(newvars_ok(Head,Body,N) -> true;
		p_message('outside newvars bound'),
		fail).

newvars_ok(Head,Body,N):-
	vars_in_term([Head],[],HVars),
	goals_to_list(Body,BodyL),
	vars_in_term(BodyL,[],BVars),
        aleph_ord_subtract(BVars,HVars,NewVars),
	length(NewVars,N1),
	N1 =< N.

get_psyms((L,B),[N/A|Syms]):-
	!,
	functor(L,N,A),
	get_psyms(B,Syms).
get_psyms(true,[]):- !.
get_psyms(L,[N/A]):-
	functor(L,N,A).


lang_ok1([],_).
lang_ok1([Pred|Preds],N):-
        length(Preds,N0),
        aleph_delete_all(Pred,Preds,Preds1),
        length(Preds1,N1),
        PredOccurs is N0 - N1 + 1,
	PredOccurs =< N,
	lang_ok1(Preds1,N).

record_pclauses([],_,[]).
record_pclauses([_-[_,_,_,Clause1]|T],CRule,[DbRef|DbRefs]):-
	(CRule = leftmost_with_delay -> 
		reorder_goals(Clause1,Clause);
		Clause = Clause1),
        split_clause(Clause,Head,Body),
        recordz(pclause,pclause(Head,Body),DbRef),
        record_pclauses(T,DbRefs).

get_user_refinement(auto,Clause,Template,0):-
	!,
	auto_refine(Clause,Template).
get_user_refinement(probabilistic,Clause,Template,Id):-
	!,
	findall(-P-R,(refine(Clause,R),find_beta_prob(refine(Clause,R),P),P>0),R1),
	probabilistic_extensions(Clause,R2),
	aleph_append(R1,R2,Refinements),
	keysort(Refinements,Sorted),
	aleph_member(_-Template,Sorted),
	(Template= (Head:-true) -> Clause1 = Head; Clause1 = Template),
	get_refine_id(refine(Clause,Clause1),Id).
get_user_refinement(user,Clause,Template,0):-
	refine(Clause,Template).

find_beta_prob(Refinement,P):-
	beta(Refinement,A,B), !,
	P is A/(A+B).
find_beta_prob(_,0.5).

% find all clauses that can be reached using 
% refinements that can be reached from the current clause
% using beta counts only. These are available from previous runsa.
probabilistic_extensions(C,L):-
	findall(P/C1,(beta(refine(C,C1),A,B),nonvar(C1),P is A/(A+B),P>0),L1),
	probabilistic_extend(L1,L1,L).

% find extensions of all clauses in a list of prob/clause pairs
probabilistic_extend([],L,L).
probabilistic_extend([_/Clause|T],LSoFar,L):-
	probabilistic_extensions(Clause,L1),
	aleph_append(L1,LSoFar,L2),
	probabilistic_extend(T,L2,L).

get_refine_id(Refinement,Id):-
	recorded(refine,refine_id(Refinement,Id),_), !.
get_refine_id(Refinement,Id):-
	gen_refine_id(Id),
	recorda(refine,refine_id(Refinement,Id),_).

match_bot(false,Clause,Clause).
match_bot(reduction,Clause,Clause1):-
	match_lazy_bottom(Clause,Lits),
	get_pclause(Lits,[],Clause1,_,_,_).
match_bot(saturation,Clause,Clause1):-
	once(get_aleph_clause(Clause,AlephClause)),
	match_bot_lits(AlephClause,[],Lits),
	get_pclause(Lits,[],Clause1,_,_,_).

match_bot_lits((Lit,Lits),SoFar,[LitNum|LitNums]):-
	!,
	match_bot_lit(Lit,LitNum),
	not(aleph_member(LitNum,SoFar)),
	match_bot_lits(Lits,[LitNum|SoFar],LitNums).
match_bot_lits(Lit,SoFar,[LitNum]):-
	match_bot_lit(Lit,LitNum),
	not(aleph_member(LitNum,SoFar)).

match_bot_lit(Lit,LitNum):-
	recorded(lits,lit_info(LitNum,_,Lit,_,_,_),_), 
	recorded(sat,bot_size(Last),_),
	LitNum =< Last.

match_lazy_bottom(Clause,SLits):-
	once(get_aleph_clause(Clause,AlephClause)),
	copy_term(Clause,CClause),
	split_clause(CClause,CHead,CBody),
	example_saturated(CHead),
	store(stage),
	set(stage,saturation),
	match_lazy_bottom1(CBody),
	reinstate(stage),
	match_bot_lits(AlephClause,[],Lits),
	sort(Lits,SLits).


match_lazy_bottom1(Body):-
	Body,
	match_body_modes(Body),
	fail.
match_lazy_bottom1(_).

match_body_modes((CLit,CLits)):-
        !,
        match_mode(body,CLit),
        match_body_modes(CLits).
match_body_modes(CLit):-
        match_mode(body,CLit).

match_mode(_,true):- !.
match_mode(Loc,CLit):-
	functor(CLit,Name,Arity),
        functor(Mode,Name,Arity),
        setting(i,IVal),
	(Loc=head ->
		recorded(aleph,modeh(_,Mode),_);
		recorded(aleph,modeb(_,Mode),_)),
        split_args(Mode,Mode,I,O,C),
        (recorded(sat,bot_size(BSize),DbRef)-> erase(DbRef); BSize = 0),
        (recorded(sat,last_lit(Last),DbRef1)-> erase(DbRef1); Last = 0),
        (Loc = head ->
        	recorda(atoms,atom(CLit,mode(Mode,O,I,C)),_),
                flatten(0,IVal,BSize,BSize1);
        	recorda(atoms,atom(CLit,mode(Mode,I,O,C)),_),
                flatten(0,IVal,BSize,BSize1)),
        recorda(sat,bot_size(BSize1),_),
        recorda(sat,last_lit(BSize1),_),
	fail.
match_mode(_,_).

% integrate head literal into lits database
% used during lazy evaluation of bottom clause
integrate_head_lit(HeadOVars):-
        example_saturated(Example),
	split_args(Example,_,_,Output,_),
	integrate_args(unknown,Example,Output),
        match_mode(head,Example),
        get_ivars1(1,ivars,lits,HeadOVars), !.
integrate_head_lit([]).


get_aleph_clause((Lit:-true),PLit):-
	!,
	get_aleph_lit(Lit,PLit).
get_aleph_clause((Lit:-Lits),(PLit,PLits)):-
	!,
	get_aleph_lit(Lit,PLit),
	get_aleph_lits(Lits,PLits).
get_aleph_clause(Lit,PLit):-
	get_aleph_lit(Lit,PLit).

get_aleph_lits((Lit,Lits),(PLit,PLits)):-
	!,
	get_aleph_lit(Lit,PLit),
	get_aleph_lits(Lits,PLits).
get_aleph_lits(Lit,PLit):-
	get_aleph_lit(Lit,PLit).

get_aleph_lit(Lit,PLit):-
	functor(Lit,Name,Arity),
	functor(PLit,Name,Arity),
	get_aleph_lit(Lit,PLit,Arity).

get_aleph_lit(_,_,0):- !.
get_aleph_lit(Lit,PLit,Arg):-
	arg(Arg,Lit,Term),
	(var(Term) -> arg(Arg,PLit,Term);arg(Arg,PLit,aleph_const(Term))),
	NextArg is Arg - 1,
	get_aleph_lit(Lit,PLit,NextArg), !.
	
% update hyperparameters of beta distrib for probabilistic refinement
update_probabilistic_refinement(_,Path,Best/_,Best1/_,Best1,_,_):-
	Best \= Best1,
	inc_beta_counts(Path,alpha), !.
update_probabilistic_refinement(_,Path,Label/_,Label/_,Label1,LMax,L):-
	Label = [_,_,_,Gain|_],
	Label1 = [_,_,_,Gain1|_],
        (Gain1 = Gain ->
		inc_beta_counts(Path,alpha);
		(LMax = L -> inc_beta_counts(Path,beta); true)).
	

% increment hyperparameters of beta distribution for each refinement
% only used if performing probabilistic refinements
inc_beta_counts([],_):- !.
inc_beta_counts([R1|R],Parameter):-
	inc_beta_count(R1,Parameter),
	inc_beta_counts(R,Parameter), !.

inc_beta_count(RefineId,Parameter):-
	recorded(refine,beta(RefineId,A,B),DbRef), !,
	erase(DbRef),
	(Parameter = beta -> A1 is A, B1 is B+1; A1 is A+1, B1 is B),
	recorda(refine,beta(RefineId,A1,B1),_).
inc_beta_count(RefineId,Parameter):-
	recorded(refine,refine_id(Clause,RefineId),_),
	beta(Clause,A,B), !,
	(Parameter = beta -> A1 is A, B1 is B+1; A1 is A+1, B1 is B),
	recorda(refine,beta(RefineId,A1,B1),_).
inc_beta_count(RefineId,Parameter):-
	(Parameter = beta -> A1 is 1, B1 is 2; A1 is 2, B1 is 1),
	recorda(refine,beta(RefineId,A1,B1),_), !.


% posonly formula as described by Muggleton, ILP-96
prove_examples(S,Flag,_,_,Entry,Best,CL,L2,Clause,Pos,Rand,PCover,RCover,[P,B,CL,I,G]):-
	arg(4,S,_/Evalfn),
	Evalfn = posonly, !,
        prove_pos(S,Flag,Entry,Best,[PC,L2],Clause,Pos,PCover,PC),
	prove_rand(S,Flag,Entry,Clause,Rand,RCover,RC),
	find_posgain(PCover,P),
	arg(16,S,M), arg(20,S,N),
	GC is (RC+1.0)/(N+2.0), % Laplace correction for small numbers
	A is log(P),
	B is log(GC),
	G is GC*M/P,
	C is CL/P,
	% Sz is CL*M/P,
	% D is M*G,
	%  I is M - D - Sz,
	I is A - B - C.
prove_examples(S,_,_,_,Entry,_,CL,_,_,Pos,Neg,Pos,Neg,[PC,NC,CL]):-
        arg(10,S,LazyOnCost),
        LazyOnCost = true, !,
        prove_lazy_cached(S,Entry,Pos,Neg,Pos1,Neg1),
        interval_count(Pos1,PC),
        interval_count(Neg1,NC).
prove_examples(S,_,_,true,Entry,_,CL,_,_,Pos,Neg,Pos,Neg,[PC,NC,CL]):-
        arg(11,S,LazyOnContra),
        LazyOnContra = true, !,
        prove_lazy_cached(S,Entry,Pos,Neg,Pos1,Neg1),
        interval_count(Pos1,PC),
        interval_count(Neg1,NC).
prove_examples(S,Flag,Path,_,Ent,Best,CL,L2,Clause,Pos,Neg,PCover,NCover,[PC,NC,CL]):-
	arg(22,S,Refine),
	Refine \= rls,
        arg(7,S,ClauseLength),
        ClauseLength = CL, !,
	interval_count(Pos,MaxPCount),
        (prove_neg(S,Flag,Ent,Best,[MaxPCount,CL],Clause,Neg,NCover,NC)-> true;
		(Refine = probabilistic ->
			Path = _-[_,_,Ids,_],
			Best \= [MaxPCount|_],
			inc_beta_counts(Ids,beta);
			true),
		fail),
        arg(17,S,Noise), arg(18,S,MinAcc),
        (maxlength_neg_ok(Noise/MinAcc,Ent,MaxPCount,NC)-> true;
		arg(22,S,Refine),
		(Refine=probabilistic -> 
			Path = _-[_,_,Ids,_],
			inc_beta_counts(Ids,beta);
		true),
		fail), 
        prove_pos(S,Flag,Ent,Best,[PC,L2],Clause,Pos,PCover,PC),
        (maxlength_neg_ok(Noise/MinAcc,Ent,PC,NC)-> true;
		(Refine=probabilistic -> inc_beta_counts(Ids,beta); true),
		fail), !.
prove_examples(S,Flag,_,_,Ent,Best,CL,L2,Clause,Pos,Neg,PCover,NCover,[PC,NC,CL]):-
        prove_pos(S,Flag,Ent,Best,[PC,L2],Clause,Pos,PCover,PC),
        prove_neg(S,Flag,Ent,Best,[PC,CL],Clause,Neg,NCover,NC),
	!.

prove_lazy_cached(S,Entry,Pos,Neg,Pos1,Neg1):-
        arg(8,S,Caching),
	Caching = true, !,
	(check_cache(Entry,pos,Pos1)->
		true;
		add_cache(Entry,pos,Pos),
		Pos1 = Pos),
	(check_cache(Entry,neg,Neg1)->
		true;
		add_cache(Entry,neg,Neg),
		Neg1 = Neg).
prove_lazy_cached(_,_,Pos,Neg,Pos,Neg).

complete_label(posonly,_,L,L):- !.
complete_label(user,Clause,[P,N,L],[P,N,L,Val]):-
        cost(Clause,[P,N,L],Cost), !,
        (Cost = inf -> Val is -10000; (Cost = -inf -> Val is 10000; Val is -Cost)).
complete_label(EvalFn,_,[P,N,L],[P,N,L,Val]):-
	evalfn(EvalFn,[P,N,L],Val), !.
complete_label(_,_,_,_):-
	p_message1('error'), p_message('incorrect evaluation/cost function'),
	fail.

% get primary and secondary search keys for search
% use [Primary|Secondary] notation as it is the most compact
get_search_keys(bf,[_,_,L,F|_],[L1|F]):-
	!,
	L1 is -1*L.
get_search_keys(df,[_,_,L,F|_],[L|F]):- !.
get_search_keys(_,[_,_,L,F|_],[F|L1]):-
	L1 is -1*L.

prove_pos(_,_,_,_,_,_,[],[],0):- !.
prove_pos(S,_,Entry,BestSoFar,PosSoFar,Clause,_,PCover,PCount):-
        recorded(covers,covers(PCover,PCount),_), !,
        pos_ok(S,Entry,BestSoFar,PosSoFar,Clause,PCover).
prove_pos(S,Flag,Entry,BestSoFar,PosSoFar,Clause,Pos,PCover,PCount):-
        prove_cache(Flag,S,pos,Entry,Clause,Pos,PCover,PCount),
        pos_ok(S,Entry,BestSoFar,PosSoFar,Clause,PCover), !.

prove_neg(S,_,Entry,_,_,_,[],[],0):-
	arg(8,S,Caching),
	(Caching = true -> add_cache(Entry,neg,[]); true), !.
prove_neg(S,Flag,Entry,_,_,Clause,Neg,NCover,NCount):-
	arg(22,S,Refine),
	Refine = rls, !,
        prove_cache(Flag,S,neg,Entry,Clause,Neg,NCover,NCount).
prove_neg(_,_,_,_,_,_,_,NCover,NCount):-
        recorded(covers,coversn(NCover,NCount),_), !.
prove_neg(S,Flag,Entry,BestSoFar,PosSoFar,Clause,Neg,NCover,NCount):-
        arg(12,S,LazyNegs),
        LazyNegs = true, !,
        lazy_prove_neg(S,Flag,Entry,BestSoFar,PosSoFar,Clause,Neg,NCover,NCount).
prove_neg(S,Flag,Entry,[P,0,L1|_],[P,L2],Clause,Neg,[],0):-
	arg(4,S,bf/coverage),
        L2 is L1 - 1,
	!,
        prove_cache(Flag,S,neg,Entry,Clause,Neg,0,[],0), !.
prove_neg(S,Flag,Entry,[P,N|_],[P,L1],Clause,Neg,NCover,NCount):-
	arg(4,S,bf/coverage),
        !,
        arg(7,S,ClauseLength),
        (ClauseLength = L1 ->
		arg(2,S,Explore),
		(Explore = true -> MaxNegs is N; MaxNegs is N - 1),
                MaxNegs >= 0,
                prove_cache(Flag,S,neg,Entry,Clause,Neg,MaxNegs,NCover,NCount),
		NCount =< MaxNegs;
                prove_cache(Flag,S,neg,Entry,Clause,Neg,NCover,NCount)),
        !.
prove_neg(S,Flag,Entry,_,[P1,L1],Clause,Neg,NCover,NCount):-
        arg(7,S,ClauseLength),
        ClauseLength = L1,  !,
        arg(17,S,Noise), arg(18,S,MinAcc),
        get_max_negs(Noise/MinAcc,P1,N1),
        prove_cache(Flag,S,neg,Entry,Clause,Neg,N1,NCover,NCount),
	NCount =< N1,
        !.
prove_neg(S,Flag,Entry,_,_,Clause,Neg,NCover,NCount):-
        prove_cache(Flag,S,neg,Entry,Clause,Neg,NCover,NCount),
        !.

prove_rand(S,Flag,Entry,Clause,Rand,RCover,RCount):-
        prove_cache(Flag,S,rand,Entry,Clause,Rand,RCover,RCount),
        !.

lazy_prove_neg(S,Flag,Entry,[P,N|_],[P,_],Clause,Neg,NCover,NCount):-
	arg(4,S,bf/coverage),
        !,
        MaxNegs is N + 1,
        prove_cache(Flag,S,neg,Entry,Clause,Neg,MaxNegs,NCover,NCount),
        !.
lazy_prove_neg(S,Flag,Entry,_,[P1,_],Clause,Neg,NCover,NCount):-
        arg(17,S,Noise), arg(18,S,MinAcc),
        get_max_negs(Noise/MinAcc,P1,N1),
        MaxNegs is N1 + 1,
        prove_cache(Flag,S,neg,Entry,Clause,Neg,MaxNegs,NCover,NCount),
        !.

get_max_negs(N/_,_,N):- number(N), !.
get_max_negs(false/A,_,0):-
        A \= false,
        A >= 0.999, !.
get_max_negs(false/MinAcc,P1,N):-
        MinAcc \= false,
        number(P1), !,
	(MinAcc = 0.0 -> N is P1 + 1;
        	NR is (1-MinAcc)*P1/MinAcc,
		N1 is integer(NR),
        	N is N1 + 1).
get_max_negs(_,_,0).


% update_open_list(+SearchKeys,+NodeRef,+Label)
% insert SearchKeys into openlist
update_open_list([K1|K2],NodeRef,Label):-
	recordz(gains,gain(K1,K2,NodeRef,Label),_),
	recorded(openlist,OpenList,DbRef),
	erase(DbRef),
	uniq_insert(descending,[K1|K2],OpenList,List1),
	recorda(openlist,List1,_).

pos_ok(S,_,_,_,_,_):-
	arg(22,S,Refine),
	(Refine = rls; Refine = user),  !.
pos_ok(S,Entry,_,[P,_],_,_):-
        arg(13,S,MinPos),
        P < MinPos, !,
        arg(8,S,Caching),
        (Caching = true ->
                add_prune_cache(Entry);
                true),
        fail.
pos_ok(S,_,[_,_,_,C1|_],[P,L],_,_):-
        arg(4,S,_/Evalfn),
        evalfn(Evalfn,[P,0,L],C2),
        (C2 > C1;
	(arg(2,S,Explore),Explore=true)), !.


maxlength_neg_ok(Noise/false,Entry,_,N):-
        !,
        (N =< Noise -> true; add_prune_cache(Entry), fail).
maxlength_neg_ok(false/Acc,Entry,P,N):-
        !,
        A is P/(P+N),
        (A >= Acc -> true; add_prune_cache(Entry), fail).
maxlength_neg_ok(_,_,_,_).

compression_ok(compression,[P,_,L|_]):-
	!,
	P - L + 1 > 0.
compression_ok(_,_).

length_ok(S,MinLen,ClauseLen,LastD,ExpectedMin,ExpectedCLen):-
        arg(3,S,RefineOp),
        (RefineOp = true  -> L1 = 0; L1 = LastD),
        (L1 < MinLen->ExpectedMin = L1;ExpectedMin = MinLen),
        ExpectedCLen is ClauseLen + ExpectedMin,
        arg(7,S,CLength),
        ExpectedCLen =< CLength, !.

update_best(S,_,_,_,Best,[_,N|_]/_,Best):-
        arg(17,S,Noise),
        Noise \= false,
        N > Noise, !.
update_best(S,_,_,_,Best,[P,N|_]/_,Best):-
        arg(18,S,MinAcc),
        MinAcc \= false,
        Accuracy is P/(P + N),
        Accuracy < MinAcc, !.
update_best(S,_,_,_,Best,[_,_,_,Compr|_]/_,Best):-
        arg(4,S,_/compression),
        Compr =< 0, !.
update_best(S,Clause,PCover,NCover,Label/_,Label1/Node1,Label1/Node1):-
        Label = [_,_,_,Gain|_],
        Label1 = [_,_,_,Gain1|_],
        Gain1 > Gain, !,
        recorded(search,selected(_,_,_,_),DbRef),
        erase(DbRef),
        recorda(search,selected(Label1,Clause,PCover,NCover),_),
        arg(35,S,VSearch),
        (VSearch = true ->
                (recorded(search,best(_),DbRef1) -> erase(DbRef1); true),
                recorda(search,best(Node1),_),
                recorda(search,good(Node1),_);
                true),
%        recorda(good,good(Label1,Clause),_),
        show_clause(Label1,Clause,Node1,newbest),
        record_clause(Label1,Clause,Node1,newbest).
update_best(S,Clause,_,_,Label/Node,Label1/Node1,Label/Node):-
%        recorda(good,good(Label1,Clause),_),
        arg(35,S,VSearch),
        (VSearch = true ->
                recorda(search,good(Node1),_);
                true),
        arg(6,S,Verbosity),
        (Verbosity >= 2 ->
                show_clause(Label1,Clause,Node1,good),
                record_clause(Label1,Clause,Node1,good);
                true).

update_best_theory(S,_,_,_,Best,[_,N|_]/_,Best):-
	arg(17,S,Noise),
	Noise \= false,
	N > Noise, !.
update_best_theory(S,_,_,_,Best,[P,N|_]/_,Best):-
	arg(18,S,MinAcc),
        MinAcc \= false,
        Accuracy is P/(P+N),
	Accuracy < MinAcc, !.
update_best_theory(_,Theory,PCover,NCover,Label/_,Label1/Node1,Label1/Node1):-
	Label = [_,_,_,Gain|_],
	Label1 = [_,_,_,Gain1|_],
	Gain1 > Gain, !, 
        recorded(search,selected(_,_,_,_),DbRef),
        erase(DbRef),
        recorda(search,selected(Label1,Theory,PCover,NCover),_),
%	recorda(good,good(Theory),_),
	show_theory(Label1,Theory,Node1,newbest),
	record_theory(Label1,Theory,Node1,newbest).
update_best_theory(S,Theory,_,_,Best,_,Best):-
%	recorda(good,good(Theory),_),
	arg(6,S,Verbosity),
	(Verbosity >= 2 ->
		show_theory(Label1,Theory,Node1,good),
		record_theory(Label1,Theory,Node1,good);
		true).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% P R U N I N G

get_node([[K1|K2]|_],DbRef,[K1|K2],Node):-
        recorded(gains,gain(K1,K2,Node,_),DbRef).
get_node([_|Gains],DbRef,Gain,Node):-
	get_node(Gains,DbRef,Gain,Node).

prune_open(S,_,_):-
	arg(25,S,OSize),
	OSize \= inf,
        retract_all(aleph_dyn,in_beam(_)),
        recorda(aleph_dyn,in_beam(0),_),
        recorded(openlist,Gains,_),
        get_node(Gains,DbRef,[K1|K2],NodeNum),
        recorded(aleph_dyn,in_beam(N),DbRef1),
        (N < OSize->
                erase(DbRef1),
                N1 is N + 1,
                recorda(aleph_dyn,in_beam(N1),_);
                erase(DbRef),
                p1_message('non-admissible removal'), p_message(NodeNum),
        	recorded(gains,gain(K1,K2,NodeNum,_),DbRef3),
                erase(DbRef3)),
        fail.
prune_open(S,_,_):-
        arg(2,S,Explore),
        arg(4,S,Search),
        arg(22,S,Refine),
	(Explore = true; not(built_in_prune(Search)); Refine = rls; Refine = mcmc), !.
prune_open(_,_/N,_/N):- !.
prune_open(S,_,[_,_,L,Best|_]/_):-
        arg(4,S,_/Evalfn),
	Evalfn = coverage, !,
	arg(27,S,Eq),
        (Eq = true -> MaxLength is L; MaxLength is L - 1),
        remove1(MaxLength,Best),
        !.
prune_open(S,_,[_,_,_,Best|_]/_):-
        arg(4,S,heuristic/Evalfn),
        (Evalfn = compression ; Evalfn = posonly), !,
        remove2(S,Best).
% pruning for laplace and m-estimates devised by James Cussens
prune_open(S,_,[_,_,L,Best|_]/_):-
        arg(4,S,_/Evalfn),
        Evalfn = laplace, !,
        arg(27,S,Eq),
        (Eq = true -> MaxLength is L; MaxLength is L - 1),
        MinPos is (Best/(1-Best))-1,
        remove1(MaxLength,MinPos).
prune_open(S,_,[_,_,L,Best|_]/_):-
        arg(4,S,_/Evalfn),
        (Evalfn = auto_m; Evalfn = mestimate), !,
        arg(27,S,Eq),
        (Eq = true -> MaxLength is L; MaxLength is L - 1),
        setting(prior,Prior),
        ((Evalfn = mestimate,setting(m,M)) ->
            MinPos is M*(Best-Prior)/(1-Best);
            MinPos is ((Best-Prior)/(1-Best))^2),
        remove1(MaxLength,MinPos).
prune_open(_,_,_).


built_in_prune(heuristic/E):-
	(E = compression; E = posonly).
built_in_prune(_/E):-
	(E = coverage; E = laplace; E = auto_m; E = mestimate).

remove1(MaxLength,Best):-
        recorded(gains,gain(_,[P,_,L1|_],_),DbRef),
        (P < Best; (P=Best,L1 >= MaxLength)),
        erase(DbRef),
        fail.
remove1(_,_).

% pruning for posonly developed in discussions with James Cussens
remove2(S,Best):-
	arg(4,S,_/Evalfn),
        recorded(gains,gain(_,[P,_,L|_],_),DbRef),
	(Evalfn = posonly ->
		arg(20,S,RSize),
		Max is log(P) + log(RSize+2.0) - (L+1)/P;
		Max is P - L + 1),
	Best >= Max,
        erase(DbRef),
        fail.
remove2(_,_).

get_nextbest(S,NodeRef):-
	arg(22,S,RefineType),
	select_nextbest(RefineType,NodeRef).

% Select the next best node
% Incorporates the changes made by Filip Zelezny to
% achieve the `randomised rapid restart' (or rrr) technique
% within randomised local search
select_nextbest(false,NodeRef):-
	recorded(search,nextnode(_),DbRef),
	erase(DbRef),
	get_nextbest(NodeRef), !.
select_nextbest(user,NodeRef):-
	recorded(search,nextnode(_),DbRef),
	erase(DbRef),
	get_nextbest(NodeRef), !.
select_nextbest(auto,NodeRef):-
	recorded(search,nextnode(_),DbRef),
	erase(DbRef),
	get_nextbest(NodeRef), !.
select_nextbest(rls,NodeRef):-
        recorded(search,nextnode(_),DbRef),
        erase(DbRef),
        setting(rls_type,Type),
        (recorded(rls,parent_stats(PStats,_,_),DbRef1)-> erase(DbRef1);
                true),
        (rls_nextbest(Type,PStats,NodeRef,Label) ->
                recorda(rls,parent_stats(Label,[],[]),_),
                setting(rls_type,RlsType),
                (RlsType = rrr ->
                      true;
                      recordz(search,nextnode(NodeRef),_));
                NodeRef = none), !.
select_nextbest(mcmc,NodeRef):-
        recorded(openlist,[H|_],DbRef),
	H = [K1|K2],
	erase(DbRef),
        recorda(openlist,[],_),
	recorded(search,nextnode(OldRef),DbRef1),
	recorded(mcmc,parent_stats([_,_,_,F|_],_,_),DbRef2),
	recorded(gains,gain(K1,K2,NewRef,Label1),DbRef3),
	erase(DbRef3),
	Label1 = [_,_,_,F1|_],
        instance(NewRef,node(_,_,_,_,PCvr1,NCvr1,_,_)),
	R is F1/(F+0.001),
	X is random,
	((R > 1; X =< R; OldRef = none) ->
		erase(DbRef1),
		erase(DbRef2),
		NodeRef = NewRef,
		recordz(search,nextnode(NodeRef),_),
		recorda(mcmc,parent_stats(Label1,PCvr1,NCvr1),_);
		NodeRef = OldRef), !.
select_nextbest(_,none).

get_nextbest(NodeRef):-
        recorded(openlist,[H|_],_),
	H = [K1|K2],
        recorded(gains,gain(K1,K2,NodeRef,_),DbRef), !,
        erase(DbRef),
        recordz(search,nextnode(NodeRef),_).
get_nextbest(NodeRef):-
        recorded(openlist,[_|T],DbRef),
        erase(DbRef),
        recorda(openlist,T,_),
        get_nextbest(NodeRef), !.
get_nextbest(none).

rls_nextbest(rrr,_,NodeRef,_):-
        get_nextbest(NodeRef).
rls_nextbest(gsat,_,NodeRef,Label):-
        recorded(openlist,[H|_],DbRef),
	H = [K1|K2],
	erase(DbRef),
	recorda(openlist,[],_),
	findall(N-L,recorded(gains,gain(K1,K2,N,L),_),Choices),
	length(Choices,Last),
	get_random(Last,N),
	remove_nth(N,Choices,NodeRef-Label,_),
	retract_all(gains).
rls_nextbest(wsat,PStats,NodeRef,Label):-
	setting(walk,WProb),
	P is random,
	P >= WProb, !,
	rls_nextbest(gsat,PStats,NodeRef,Label).
rls_nextbest(wsat,PStats,NodeRef,Label):-
	p_message('random walk'),
        recorded(openlist,_,DbRef),
	erase(DbRef),
	recorda(openlist,[],_),
	findall(N-L,recorded(gains,gain(_,_,N,L),_),AllNodes),
	potentially_good(AllNodes,PStats,Choices),
        length(Choices,Last),
        get_random(Last,N),
        remove_nth(N,Choices,NodeRef-Label,_),
	retract_all(gains).
rls_nextbest(anneal,[P,N|_],NodeRef,Label):-
	setting(temperature,Temp),
        recorded(openlist,_,DbRef),
	erase(DbRef),
	recorda(openlist,[],_),
	findall(N-L,recorded(gains,gain(_,_,N,L),_),AllNodes),
	length(AllNodes,Last),
	get_random(Last,S),
	remove_nth(S,AllNodes,NodeRef-Label,_),
	Label = [P1,N1|_],
	Gain is (P1 - N1) - (P - N),
	((P = 1); (Gain >= 0);(R is random, R < exp(Gain/Temp))).

% mcmc_nextbest([_,_,_,F|_],NodeRef,Label,PCvr,NCvr):-

potentially_good([],_,[]).
potentially_good([H|T],Label,[H|T1]):-
        H = _-Label1,
        potentially_good(Label,Label1), !,
        potentially_good(T,Label,T1).
potentially_good([_|T],Label,T1):-
        potentially_good(T,Label,T1).

potentially_good([1|_],[P1|_]):-
        !,
        P1 > 1.
potentially_good([P,_,L|_],[P1,_,L1|_]):-
        L1 =< L, !,
        P1 > P.
potentially_good([_,N|_],[_,N1|_]):-
        N1 < N.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% P R O V E

% prove with caching
% if entry exists in cache, then return it
% otherwise find and cache cover 
% if ``exact'' flag is set then only check proof for examples
% in the part left over due to lazy theorem-proving
% ideas in caching developed in discussions with James Cussens

prove_cache(exact,S,Type,Entry,Clause,Intervals,IList,Count):-
	!,
	(Intervals = Exact/Left ->
        	arg(14,S,Depth),
        	arg(29,S,Time),
        	prove(Depth/Time,Type,Clause,Left,IList1,Count1),
		aleph_append(IList1,Exact,IList),
		interval_count(Exact,Count0),
		Count is Count0 + Count1;
		IList = Intervals,
		interval_count(IList,Count)),
        arg(8,S,Caching),
        (Caching = true -> add_cache(Entry,Type,IList); true).
prove_cache(upper,S,Type,Entry,Clause,Intervals,IList,Count):-
        arg(8,S,Caching),
        Caching = true, !,
        arg(14,S,Depth),
        arg(29,S,Time),
        (check_cache(Entry,Type,Cached)->
                prove_cached(S,Type,Entry,Cached,Clause,Intervals,IList,Count);
                prove_intervals(Depth/Time,Type,Clause,Intervals,IList,Count),
                add_cache(Entry,Type,IList)).
prove_cache(upper,S,Type,_,Clause,Intervals,IList,Count):-
        arg(14,S,Depth),
        arg(29,S,Time),
	(Intervals = Exact/Left ->
		aleph_append(Left,Exact,IList1),
        	prove(Depth/Time,Type,Clause,IList1,IList,Count);
        	prove(Depth/Time,Type,Clause,Intervals,IList,Count)).

prove_intervals(DepthTime,Type,Clause,I1/Left,IList,Count):- 
	!,
	aleph_append(Left,I1,Intervals),
	prove(DepthTime,Type,Clause,Intervals,IList,Count).
prove_intervals(DepthTime,Type,Clause,Intervals,IList,Count):- 
	prove(DepthTime,Type,Clause,Intervals,IList,Count).

prove_cached(S,Type,Entry,I1/Left,Clause,Intervals,IList,Count):-
        !,
        arg(14,S,Depth),
        arg(29,S,Time),
        prove(Depth/Time,Type,Clause,Left,I2,_),
        aleph_append(I2,I1,I),
        (Type = pos ->
                arg(5,S,Greedy),
                (Greedy = true ->
                        intervals_intersection(I,Intervals,IList);
                        IList = I);
                IList = I),
        interval_count(IList,Count),
        update_cache(Entry,Type,IList).
prove_cached(S,Type,Entry,I1,_,Intervals,IList,Count):-
	(Type = pos -> arg(5,S,Greedy),
		(Greedy = true ->
			intervals_intersection(I1,Intervals,IList);
			IList = I1);
		IList = I1),
	interval_count(IList,Count),
	update_cache(Entry,Type,IList).

% prove at most Max atoms
prove_cache(exact,S,Type,Entry,Clause,Intervals,Max,IList,Count):-
	!,
	(Intervals = Exact/Left ->
		interval_count(Exact,Count0),
		Max1 is Max - Count0,
        	arg(12,S,LNegs),
        	arg(14,S,Depth),
        	arg(29,S,Time),
        	prove(LNegs/false,Depth/Time,Type,Clause,Left,Max1,IList1,Count1),
		aleph_append(IList1,Exact,Exact1),
		find_lazy_left(S,Type,Exact1,Left1),
		IList = Exact1/Left1,
		Count is Count0 + Count1;
		IList = Intervals,
		interval_count(Intervals,Count)),
        arg(8,S,Caching),
        (Caching = true -> add_cache(Entry,Type,IList); true).
prove_cache(upper,S,Type,Entry,Clause,Intervals,Max,IList,Count):-
        arg(8,S,Caching),
        Caching = true, !,
        (check_cache(Entry,Type,Cached)->
                prove_cached(S,Type,Entry,Cached,Clause,Intervals,Max,IList,Count);
                (prove_intervals(S,Type,Clause,Intervals,Max,IList1,Count)->
                        find_lazy_left(S,Type,IList1,Left1),
                        add_cache(Entry,Type,IList1/Left1),
			IList = IList1/Left1,
                        retract_all(aleph_dyn,example_cache(_));
                        collect_example_cache(IList),
                        add_cache(Entry,Type,IList),
                        fail)).
prove_cache(upper,S,Type,_,Clause,Intervals,Max,IList/Left1,Count):-
        arg(8,S,Caching),
        arg(12,S,LNegs),
        arg(14,S,Depth),
        arg(29,S,Time),
	(Intervals = Exact/Left ->
		aleph_append(Left,Exact,IList1),
        	prove(LNegs/Caching,Depth/Time,Type,Clause,IList1,Max,IList,Count);
        	prove(LNegs/Caching,Depth/Time,Type,Clause,Intervals,Max,IList,Count)),
	find_lazy_left(S,Type,IList,Left1).

prove_intervals(S,Type,Clause,I1/Left,Max,IList,Count):-
        !,
        arg(8,S,Caching),
        arg(12,S,LNegs),
        arg(14,S,Depth),
        arg(29,S,Time),
        aleph_append(Left,I1,Intervals),
        prove(LNegs/Caching,Depth/Time,Type,Clause,Intervals,Max,IList,Count).
prove_intervals(S,Type,Clause,Intervals,Max,IList,Count):-
        arg(8,S,Caching),
        arg(12,S,LNegs),
        arg(14,S,Depth),
        arg(29,S,Time),
        prove(LNegs/Caching,Depth/Time,Type,Clause,Intervals,Max,IList,Count).


prove_cached(S,Type,Entry, I1/Left,Clause,_,Max,IList/Left1,Count):-
        !,
        arg(8,S,Caching),
        arg(12,S,LNegs),
        arg(14,S,Depth),
        arg(29,S,Time),
        interval_count(I1,C1),
        Max1 is Max - C1,
        Max1 >= 0,
        (prove(LNegs/Caching,Depth/Time,Type,Clause,Left,Max1,I2,C2)->
                aleph_append(I2,I1,IList),
                Count is C2 + C1,
                find_lazy_left(S,Type,IList,Left1),
                update_cache(Entry,Type,IList/Left1),
                retract_all(aleph_dyn,example_cache(_));
                collect_example_cache(I2/Left1),
                aleph_append(I2,I1,IList),
                update_cache(Entry,Type,IList/Left1),
                fail).
prove_cached(_,neg,_, I1/L1,_,_,_,I1/L1,C1):-
	!,
	interval_count(I1,C1).
prove_cached(S,_,_,I1,_,_,Max,I1,C1):-
	interval_count(I1,C1),
	arg(12,S,LNegs),
	(LNegs = true ->true; C1 =< Max).

collect_example_cache(Intervals/Left):-
	recorded(aleph_dyn,example_cache([Last|Rest]),DbRef), 
	erase(DbRef),
	aleph_reverse([Last|Rest],IList),
	list_to_intervals1(IList,Intervals),
	Next is Last + 1,
	recorded(aleph,size(neg,LastN),_),
	(Next > LastN -> Left = []; Left = [Next-LastN]).

find_lazy_left(S,_,_,[]):-
        arg(12,S,LazyNegs),
        LazyNegs = false, !.
find_lazy_left(_,_,[],[]).
find_lazy_left(S,Type,[_-F],Left):-
        !,
        F1 is F + 1,
	(Type = pos -> arg(16,S,Last);
		(Type = neg -> arg(24,S,Last);
			(Type = rand -> arg(20,S,Last); Last = F))),
        (F1 > Last -> Left = []; Left = [F1-Last]).
find_lazy_left(S,Type,[_|T1],Left):-
        find_lazy_left(S,Type,T1,Left).


% prove atoms specified by Type and index set using Clause.
% dependent on data structure used for index set:
% currently index set is a list of intervals
% return atoms proved and their count
% if tail-recursive version is needed see below

prove(_,_,_,[],[],0).
prove(DepthTime,Type,Clause,[Interval|Intervals],IList,Count):-
	index_prove(DepthTime,Type,Clause,Interval,I1,C1),
	prove(DepthTime,Type,Clause,Intervals,I2,C2),
	aleph_append(I2,I1,IList),
	Count is C1 + C2.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% T A I L - R E C U R S I V E  P R O V E/6
 
% use this rather than the prove/6 above for tail recursion
% written by James Cussens
 

% prove(DepthTime,Type,Clause,Intervals,IList,Count):-
       % prove2(Intervals,DepthTime,Type,Clause,0,IList,Count).
 
% code for tail recursive cover testing
% starts here

% when we know that Sofar is a variable.
prove2([],_,_,_,Count,[],Count).
prove2([Current-Finish|Intervals],Depth/Time,Type,(Head:-Body),InCount,Sofar,OutCount) :-
%       \+ ((example(Current,Type,Head),resource_bound_call(Time,Depth,Body))), %uncovered
% ICD: added for the nuclear smuggling
        (Head = linked(A,B) ->
            (\+ (((example(Current,Type,linked(A,B)),depth_bound_call(Body,Depth))); 
                 ((example(Current,Type,linked(B,A)),depth_bound_call(Body,Depth)))))
	                    ;
             \+ ((example(Current,Type,Head),depth_bound_call(Body,Depth))) %uncovered
	),
% end of my modif
        !,
        (Current>=Finish ->
            prove2(Intervals,Depth/Time,Type,(Head:-Body),InCount,Sofar,OutCount);
            Next is Current+1,!,
            prove2([Next-Finish|Intervals],Depth/Time,Type,(Head:-Body),InCount,Sofar,OutCount)
        ).
prove2([Current-Finish|Intervals],Depth/Time,Type,Clause,InCount,Sofar,OutCount) :-
        (Current>=Finish ->
            Sofar=[Current-Current|Rest],
            MidCount is InCount+1,!,
            prove2(Intervals,Depth/Time,Type,Clause,MidCount,Rest,OutCount);
            Next is Current+1,
            Sofar=[Current-_Last|_Rest],!,
            prove3([Next-Finish|Intervals],Depth/Time,Type,Clause,InCount,Sofar,OutCount)
        ).
 
 
%when Sofar is not a variable
prove3([Current-Finish|Intervals],Depth/Time,Type,(Head:-Body),InCount,Sofar,OutCount) :-
%       \+ ((example(Current,Type,Head),resource_bound_call(Time,Depth,Body))), %uncovered
% ICD: added for the nuclear smuggling
        (Head = linked(A,B) ->
            (\+ (((example(Current,Type,linked(A,B)),depth_bound_call(Body,Depth))); 
                 ((example(Current,Type,linked(B,A)),depth_bound_call(Body,Depth)))))
	                    ;
             \+ ((example(Current,Type,Head),depth_bound_call(Body,Depth))) %uncovered
	),
% end of my modif 
        !,
        Last is Current-1, %found some previously
        Sofar=[Start-Last|Rest], %complete found interval
        MidCount is InCount+Current-Start,
        (Current>=Finish ->
            prove2(Intervals,Depth/Time,Type,(Head:-Body),MidCount,Rest,OutCount);
            Next is Current+1,!,
            prove2([Next-Finish|Intervals],Depth/Time,Type,(Head:-Body),MidCount,Rest,OutCount)
        ).
prove3([Current-Finish|Intervals],Depth/Time,Type,Clause,InCount,Sofar,OutCount) :-
        (Current>=Finish ->
            Sofar=[Start-Finish|Rest],
            MidCount is InCount+Finish-Start+1,!,
            prove2(Intervals,Depth/Time,Type,Clause,MidCount,Rest,OutCount);
            Next is Current+1,!,
            prove3([Next-Finish|Intervals],Depth/Time,Type,Clause,InCount,Sofar,OutCount)
        ).
 
 
% code for tail recursive cover testing
% ends here

 

index_prove(_,_,_,Start-Finish,[],0):-
	Start > Finish, !.
index_prove(Depth/Time,Type,Clause,Start-Finish,IList,Count):-
	index_prove1(Depth/Time,Type,Clause,Start,Finish,Last),
	Last0 is Last - 1 ,
	Last1 is Last + 1,
	(Last0 >= Start->
		index_prove(Depth/Time,Type,Clause,Last1-Finish,Rest,Count1),
		IList = [Start-Last0|Rest],
		Count is Last - Start + Count1;
		index_prove(Depth/Time,Type,Clause,Last1-Finish,IList,Count)).

prove1(G):-
	depth_bound_call(G), !.
	
index_prove1(_,_,_,Num,Last,Num):-
	Num > Last, !.
index_prove1(Depth/Time,Type,(Head:-Body),Num,Finish,Last):-
%	\+((\+((example(Num,Type,Head),resource_bound_call(Time,Depth,Body))))), !,
% ICD: added for the nuclear smuggling
        (Head = linked(A,B) ->
            (\+((\+(((example(Num,Type,linked(A,B)),depth_bound_call(Body,Depth)); 
                     (example(Num,Type,linked(B,A)),depth_bound_call(Body,Depth)))))))
	                    ;
  	     \+((\+((example(Num,Type,Head),depth_bound_call(Body,Depth)))))
	), !,
% end of my modif 
	Num1 is Num + 1,
	index_prove1(Depth/Time,Type,(Head:-Body),Num1,Finish,Last).
index_prove1(_,_,_,Last,_,Last).


% proves at most Max atoms using Clause.

prove(_,_,_,_,[],_,[],0).
prove(Flags,Depth/Time,Type,Clause,[Interval|Intervals],Max,IList,Count):-
        index_prove(Flags,Depth/Time,Type,Clause,Interval,Max,I1,C1), !,
        Max1 is Max - C1,
        prove(Flags,Depth/Time,Type,Clause,Intervals,Max1,I2,C2),
        aleph_append(I2,I1,IList),
        Count is C1 + C2.


index_prove(_,_,_,_,Start-Finish,_,[],0):-
        Start > Finish, !.
index_prove(Flags,Depth/Time,Type,Clause,Start-Finish,Max,IList,Count):-
        index_prove1(Flags,Depth/Time,Type,Clause,Start,Finish,0,Max,Last),
        Last0 is Last - 1 ,
        Last1 is Last + 1,
        (Last0 >= Start->
                Max1 is Max - Last + Start,
		((Max1 = 0, Flags = true/_) ->
                        Rest = [], Count1 = 0;
                	index_prove(Flags,Depth/Time,Type,Clause,Last1-Finish,
					Max1,Rest,Count1)),
                IList = [Start-Last0|Rest],
                Count is Last - Start + Count1;
                index_prove(Flags,Depth/Time,Type,Clause,Last1-Finish,Max,IList,Count)).

index_prove1(false/_,_,_,_,_,_,Proved,Allowed,_):-
        Proved > Allowed, !, fail.
index_prove1(_,_,_,_,Num,Last,_,_,Num):-
        Num > Last, !.
index_prove1(true/_,_,_,_,Num,_,Allowed,Allowed,Num):- !.
index_prove1(LNegs/Caching,Depth/Time,Type,(Head:-Body),Num,Finish,Proved,Allowed,Last):-
        \+((\+((example(Num,Type,Head),depth_bound_call(Body,Depth))))), !,
        Num1 is Num + 1,
        Proved1 is Proved + 1,
        (Caching = true ->
                (recorded(aleph_dyn,example_cache(L),DbRef)->
                        erase(DbRef),
                        recorda(aleph_dyn,example_cache([Num|L]),_);
                        recorda(aleph_dyn,example_cache([Num]),_));
                true),
        index_prove1(LNegs/Caching,Depth/Time,Type,(Head:-Body),Num1,Finish,Proved1,Allowed,Last).
index_prove1(_,_,_,_,Last,_,_,_,Last).

% general prove at least Min atoms using Clause.
prove_at_least(Type,Clause,Min,Cover,C):-
        split_clause(Clause,Head,Body),
        recordz(pclause,pclause(Head,Body),DbRef),
        recorded(aleph,atoms(Type,Atoms),_),
        recorded(aleph,set(depth,Depth),_),
        (recorded(aleph,set(prooftime,Time),_) -> true; Time = inf),
        prove(Depth/Time,Type,(Head:-Body),Atoms,Cover,C),
        erase(DbRef),
        C >= Min.

% general prove at most Max atoms using Clause.
prove_at_most(Type,Clause,Max,Cover,C):-
        split_clause(Clause,Head,Body),
        recordz(pclause,pclause(Head,Body),DbRef),
        recorded(aleph,atoms(Type,Atoms),_),
        N1 is Max + 1,
        recorded(aleph,set(depth,Depth),_),
        (recorded(aleph,set(prooftime,Time),_) -> true; Time = inf),
        prove(Depth/Time,Type,(Head:-Body),Atoms,N1,Cover,C),
        erase(DbRef),
        C =< Max.

% resource_bound_call(Time,Depth,Goals)
%	attempt to prove Goals using depth bounded theorem-prover
%	in at most Time secs
resource_bound_call(inf,Depth,Goals):-
	!,
	depth_bound_call(Goals,Depth).
resource_bound_call(T,Depth,Goals):-
	catch(timed_depth_bound_call(T,Depth,Goals), prooflimit,fail).

timed_depth_bound_call(T,Depth,Goals):-
	alarm(T,throw(prooflimit),_),
	(depth_bound_call(Goals,Depth) ->
		alarm(0,throw(prooflimit),_) ; alarm(0,throw(prooflimit),_), fail).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% C A C H I N G

clear_cache:-
	retract_all(cache),
	retract_all(prune_cache).

check_cache(Entry,Type,I):-
	Entry \= false,
        recorded(cache,Entry,_), !,
        functor(Entry,_,Arity),
        (Type = pos -> Arg is Arity - 1; Arg is Arity),
        arg(Arg,Entry,I),
        not(var(I)).

add_cache(false,_,_):- !.
add_cache(Entry,Type,I):-
        (recorded(cache,Entry,DbRef)-> erase(DbRef); true),
        functor(Entry,_,Arity),
        (Type = pos -> Arg is Arity - 1; Arg is Arity),
        (arg(Arg,Entry,I)-> recorda(cache,Entry,_);
                        true), !.

update_cache(Entry,Type,I):-
        Entry \= false,
        functor(Entry,Name,Arity),
        (Type = pos -> Arg is Arity - 1; Arg is Arity),
        arg(Arg,Entry,OldI),
        OldI = _/_,
        recorded(cache,Entry,DbRef),
        erase(DbRef),
        functor(NewEntry,Name,Arity),
        Arg0 is Arg - 1,
        copy_args(Entry,NewEntry,1,Arg0),
        arg(Arg,NewEntry,I),
        Arg1 is Arg + 1,
        copy_args(Entry,NewEntry,Arg1,Arity),
        recorda(cache,NewEntry,_), !.
update_cache(_,_,_).

	
add_prune_cache(false):- !.
add_prune_cache(Entry):-
	(recorded(aleph,set(caching,true),_)->
		functor(Entry,_,Arity),
		A1 is Arity - 2,
		arg(A1,Entry,Clause),
		recorda(prune_cache,prune(Clause),_);
		true).

get_cache_entry(Max,Clause,Entry):-
        skolemize(Clause,Head,Body,0,_),
	length(Body,L1),
	Max >= L1 + 1,
        hash_term([Head|Body],Entry), !.
get_cache_entry(_,_,false).

% upto 3-argument indexing using predicate names in a clause
hash_term([L0,L1,L2,L3,L4|T],Entry):-
        !,
        functor(L1,P1,_), functor(L2,P2,_),
        functor(L3,P3,_), functor(L4,P4,_),
        functor(Entry,P4,6),
        arg(1,Entry,P2), arg(2,Entry,P3),
        arg(3,Entry,P1), arg(4,Entry,[L0,L1,L2,L3,L4|T]).
hash_term([L0,L1,L2,L3],Entry):-
        !,
        functor(L1,P1,_), functor(L2,P2,_),
        functor(L3,P3,_),
        functor(Entry,P3,5),
        arg(1,Entry,P2), arg(2,Entry,P1),
        arg(3,Entry,[L0,L1,L2,L3]).
hash_term([L0,L1,L2],Entry):-
        !,
        functor(L1,P1,_), functor(L2,P2,_),
        functor(Entry,P2,4),
        arg(1,Entry,P1), arg(2,Entry,[L0,L1,L2]).
hash_term([L0,L1],Entry):-
        !,
        functor(L1,P1,_),
        functor(Entry,P1,3),
        arg(1,Entry,[L0,L1]).
hash_term([L0],Entry):-
        functor(L0,P0,_),
        functor(Entry,P0,3),
        arg(1,Entry,[L0]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% G C W S

% examine list of clauses to be specialised
% generate an exception theory for each clause that covers negative examples
gcws:-
	setting(evalfn,EvalFn),
	repeat,
	recorded(specialise,hypothesis([P,N,L|T],Clause,PCover,NCover),DbRef),
	erase(DbRef),
	(PCover = _/_ -> label_create(pos,Clause,Label1),
		extract_pos(Label1,PCover1),
		interval_count(PCover1,P1);
		PCover1 = PCover,
		P1 = P),
	(NCover = _/_ -> label_create(neg,Clause,Label2),
		extract_neg(Label2,NCover1),
		interval_count(NCover1,N1);
		NCover1 = NCover,
		N1 = N),
	(N1 = 0 -> NewClause = Clause, NewLabel = [P1,N1,L|T];
		MinAcc is P1/(2*P1 - 1),
		set(minacc,MinAcc),
		gcws(Clause,PCover1,NCover1,NewClause),
		L1 is L + 1,
		complete_label(EvalFn,NewClause,[P,0,L1],NewLabel)),
	recordz(gcws,hypothesis(NewLabel,NewClause,PCover1,[]),_),
	not(recorded(specialise,hypothesis(_,_,_,_),_)), !.


% gcws(+Clause,+PCvr,+NCvr,-Clause1)
%	specialise Clause that covers pos examples PCvr and neg examples NCvr
%	result is is Clause extended with a single negated literal
% clauses in exception theory are added to list for specialisation
gcws(Clause,PCover,NCover,Clause1):-
	gen_absym(AbName),
	split_clause(Clause,Head,Body),
	functor(Head,_,Arity),
	add_determinations(AbName/Arity),
	add_modes(AbName/Arity),
	gen_ab_examples(AbName/Arity,PCover,NCover),
	cwinduce,
	Head =.. [_|Args],
	AbLit =.. [AbName|Args],
	(Body = true -> Body1 = not(AbLit) ; app_lit(not(AbLit),Body,Body1)),
	Clause1 = (Head:-Body1).

% greedy set-cover based construction of abnormality theory 
% starts with the first exceptional example
% each clause obtained is added to list of clauses to be specialised 
cwinduce:-
	store(greedy),
        set(greedy,true),
        recorded(aleph,atoms_left(pos,PosSet),_),
        not(PosSet = []),
        repeat,
	recorded(aleph,atoms_left(pos,[Num-X|Y]),DbRef),
	sat(Num),
	reduce,
	recorded(aleph,hypothesis(Label,H,PCover,NCover),DbRef1),
	erase(DbRef1),
	recorda(specialise,hypothesis(Label,H,PCover,NCover),_),
        rm_seeds1(PCover,[Num-X|Y],NewPosLeft),
	erase(DbRef),
        recorda(aleph,atoms_left(pos,NewPosLeft),DbRef3),
	NewPosLeft = [],
	erase(DbRef3),
	reinstate(greedy), !.
cwinduce.

% add_determinations(+PSym)
% add determination declarations for new abnormality predicate
% these are obtained from the determinations of the target predicate
% currently only allows stratified non-recursive definitions for ab pred
add_determinations(PSym):-
	recorded(aleph,targetpred(Target),_),
	determinations(Target,OtherPred),
	OtherPred \= Target,
	determination(PSym,OtherPred),
	fail.
add_determinations(_).

% add_modes(+PSym)
% add modes declarations for new abnormality predicate
% these are obtained from the modes of the target predicate
add_modes(Name/_):-
	recorded(aleph,targetpred(Target),_),
	modes(Target,Mode),
	Mode =.. [ModeType,Recall,TargetMode],
	TargetMode =.. [_|Args],
	AbMode =.. [Name|Args],
	NewMode =.. [ModeType,Recall,AbMode],
	call(NewMode),
	fail.
add_modes(_).

% gen_ab_examples(+Ab,+PCover,+NCover)
% obtain examples for abnormality predicate Ab by
%	pos examples are copies of neg examples in NCover
%	neg examples are copies of pos examples in PCover
% writes new examples to temporary ".f" and ".n" files
% to ensure example/3 remains a static predicate
% alters search parameters accordingly
gen_ab_examples(Ab/_,PCover,NCover):-
	concat(['.alephtmp','.f'],PosFile),
	concat(['.alephtmp','.n'],NegFile),
	create_examples(PosFile,Ab,neg,NCover,pos,PCover1),
	create_examples(NegFile,Ab,pos,PCover,neg,NCover1),
	consult(PosFile),
	consult(NegFile),
        retract_all(aleph,atoms_left(_,_)),
        retract_all(aleph,size(_,_)),
        recorda(aleph,atoms_left(pos,PCover1),_),
        recorda(aleph,atoms_left(neg,NCover1),_),
        interval_count(PCover1,PSize),
        interval_count(NCover1,NSize),
        recorda(aleph,size(pos,PSize),_),
        recorda(aleph,size(neg,NSize),_).

% create_examples(+File,+OldType,+OldE,+NewType,-NewE)
% copy OldE examples of OldType to give NewE examples of NewType 
% copy stored in File
create_examples(File,Ab,OldT,OldE,NewT,[Next-Last]):-
	recorded(aleph,last_example(NewT,OldLast),DbRef),
	open(File,write,Stream),
	set_output(Stream),
	create_copy(OldE,OldT,NewT,Ab,OldLast,Last),
	close(Stream),
	set_output(user_output),
	Last > OldLast, !,
	erase(DbRef),
	Next is OldLast + 1,
	recorda(aleph,last_example(NewT,Last),_).
create_examples(_,_,_,_,_,[]).

create_copy([],_,_,_,L,L).
create_copy([X-Y|T],OldT,NewT,Ab,Num,Last):-
	(X > Y ->
		create_copy(T,OldT,NewT,Ab,Num,Last);
		example(X,OldT,Example),
		Example =.. [_|Args],
		NewExample =.. [Ab|Args],
		Num1 is Num + 1,
		writeq(example(Num1,NewT,NewExample)), write('.'), nl,
		X1 is X + 1,
		create_copy([X1-Y|T],OldT,NewT,Ab,Num1,Last)).

% gen_absym(-Name)
% generate new abnormality predicate symbol
gen_absym(Name):-
	(recorded(aleph,last_ab(N),DbRef) ->
		erase(DbRef),
		N1 is N + 1;
		N1 is 0),
	recorda(aleph,last_ab(N1),_),
	concat([ab,N1],Name).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% C L A U S E   O P T I M I S A T I O N S

optimise(Clause,Clause1):-
	remove_redundant(Clause,Clause0),
	reorder_clause(Clause0,Clause1).
	% pre_compile(Clause1).

remove_redundant((Head:-Body),(Head1:-Body1)):-
	goals_to_list((Head,Body),ClauseL),
	remove_subsumed(ClauseL,[Head1|Body1L]),
	(Body1L = [] -> Body1 = true; list_to_goals(Body1L,Body1)).

reorder_clause((Head:-Body), Clause) :-
        % term_variables(Head,LHead),
        vars_in_term([Head],[],LHead),
        number_goals_and_get_vars(Body,LHead,1,_,[],Conj),
        calculate_independent_sets(Conj,[],BSets),
        compile_clause(BSets,Head,Clause).

reorder_goals((Head:-Body),(Head:-Body1)):-
	!,
        vars_in_term([Head],[],LHead),
        number_goals_and_get_vars(Body,LHead,1,_,[],Conj),
	reorder_goals_in_set(Conj,[],Conj1),
	glist_to_goals(Conj1,Body1).
reorder_goals(Head,Head).

number_goals_and_get_vars((G,Body),LHead,I0,IF,L0,[g(I0,LVF,NG)|LGs]) :- !,
        I is I0+1,
        get_goal_vars(G,LHead,LVF,NG),
        number_goals_and_get_vars(Body,LHead,I,IF,L0,LGs).
number_goals_and_get_vars(G,LHead,I,I,L0,[g(I,LVF,NG)|L0]) :-
        get_goal_vars(G,LHead,LVF,NG).

get_goal_vars(G,LHead,LVF,G) :-
        % term_variables(G,LV0),
        vars_in_term([G],[],LVI),
        aleph_ord_subtract(LVI,LHead,LVF).

calculate_independent_sets([],BSets,BSets).
calculate_independent_sets([G|Ls],BSets0,BSetsF) :-
        add_goal_to_set(G,BSets0,BSetsI),
        calculate_independent_sets(Ls,BSetsI,BSetsF).

add_goal_to_set(g(I,LV,G),Sets0,SetsF) :-
        add_to_sets(Sets0,LV,[g(I,LV,G)],SetsF).

add_to_sets([],LV,Gs,[[LV|Gs]]).
add_to_sets([[LV|Gs]|Sets0],LVC,GsC,[[LV|Gs]|SetsF]) :-
        aleph_ord_disjoint(LV,LVC), !,
        add_to_sets(Sets0,LVC,GsC,SetsF).
add_to_sets([[LV|Gs]|Sets0],LVC,GsC,SetsF) :-
        aleph_ord_union(LV,LVC,LVN),
        join_goals(Gs,GsC,GsN),
        add_to_sets(Sets0,LVN,GsN,SetsF).

join_goals([],L,L):- !.
join_goals(L,[],L):- !.
join_goals([g(I1,VL1,G1)|T],[g(I2,VL2,G2)|T2],Z) :-
        I1 < I2, !,
        Z = [g(I1,VL1,G1)|TN],
        join_goals(T,[g(I2,VL2,G2)|T2],TN).
join_goals([H|T],[g(I2,VL2,G2)|T2],Z) :-
        Z = [g(I2,VL2,G2)|TN],
        join_goals(T,[H|T2],TN).

reorder_goals_in_set([],_,[]):- !.
reorder_goals_in_set(Goals,V0,[g(I,V,G)|Rest]):-
	score_goals_in_set(Goals,V0,Scored),
	keysort(Scored,[_-g(I,V,G)|_]),
	aleph_ord_union(V0,V,V1),
	aleph_delete(g(I,V,G),Goals,Goals1),
	reorder_goals_in_set(Goals1,V1,Rest).

score_goals_in_set([],_,[]).
score_goals_in_set([g(I,V,G)|Goals1],V0,[N-g(I,V,G)|Rest]):-
	aleph_ord_intersection(V,V0,VI),
	length(V,NV),
	length(VI,NI),
	N is NV - NI,
	score_goals_in_set(Goals1,V0,Rest).

compile_clause(Goals,Head,(Head:-Body)):-
        compile_clause2(Goals,Body).

compile_clause2([[_|B]], B1):-
	!,
        glist_to_goals(B,B1).
compile_clause2([[_|B]|Bs],(B1,!,NB)):-
        glist_to_goals(B,B1),
        compile_clause2(Bs,NB).

glist_to_goals([g(_,_,Goal)],Goal):- !.
glist_to_goals([g(_,_,Goal)|Goals],(Goal,Goals1)):-
        glist_to_goals(Goals,Goals1).

% remove literals subsumed in the body of a clause
remove_subsumed([Head|Lits],Lits1):-
	delete(Lit,Lits,Left),
	\+(\+(redundant(Lit,[Head|Lits],[Head|Left]))), !,
	remove_subsumed([Head|Left],Lits1).
remove_subsumed(L,L).

% determine if Lit is subsumed by a body literal
redundant(Lit,Lits,[Head|Body]):-
	copy_term([Head|Body],Rest1),
	member(Lit1,Body),
	Lit = Lit1,
	aleph_subsumes(Lits,Rest1).

aleph_subsumes(Lits,Lits1):-
	\+(\+((numbervars(Lits,0,_),numbervars(Lits1,0,_),aleph_subset1(Lits,Lits1)))).

pre_compile(Clause):-
	split_clause(Clause,Head,Body),
	abolish(pclause,1),
	assert_static((pclause(Head):- Body)).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% S A T  /  R E D U C E

sat(Num):-
	integer(Num),
	example(Num,pos,_),
	sat(pos,Num), !.
sat(Example):-
	record_example(check,uspec,Example,Num),
	sat(uspec,Num), !.
	

sat(Type,Num):-
        setting(construct_bottom,false), !,
        sat_prelims,
	example(Num,Type,Example),
	p1_message('sat'), p_message(Num), p_message(Example),
	record_sat_example(Num),
	recorda(sat,sat(Num,Type),_),
	recorda(sat,head_ovars([]),_).
sat(Type,Num):-
	setting(lazy_bottom,true), !,
	sat_prelims,
	example(Num,Type,Example),
	p1_message('sat'), p_message(Num), p_message(Example),
	record_sat_example(Num),
	recorda(sat,sat(Num,Type),_),
	integrate_head_lit(HeadOVars),
	recorda(sat,head_ovars(HeadOVars),_).
sat(Type,Num):-
	set(stage,saturation),
	sat_prelims,
	example(Num,Type,Example),
	p1_message('sat'), p_message(Num), p_message(Example),
	record_sat_example(Num),
	recorda(sat,sat(Num,Type),_),
	split_args(Example,Mode,Input,Output,Constants),
	integrate_args(unknown,Example,Output),
	StartClock is cputime,
	recordz(atoms,atom(Example,mode(Mode,Output,Input,Constants)),_),
	recorded(aleph,set(i,Ival),_),
	flatten(0,Ival,0,Last1),
	recorded(lits,lit_info(1,_,Atom,_,_,_),_),
	get_vars(Atom,Output,HeadOVars),
	recorda(sat,head_ovars(HeadOVars),_),
	get_vars(Atom,Input,HeadIVars),
	recorda(sat,head_ivars(HeadIVars),_),
	functor(Example,Name,Arity), 
	get_determs(Name/Arity,L),
format("Determs: ~w~n",[L]),
	(recorded(aleph,determination(Name/Arity,'='/2),_)->
		recorda(sat,set(eq,true),_);
		recorda(sat,set(eq,false),_)),
	get_atoms(L,1,Ival,Last1,Last),
	StopClock is cputime,
	Time is StopClock - StartClock,
	recorda(sat,last_lit(Last),_),
	recorda(sat,bot_size(Last),_),
	update_generators,
	rm_moderepeats(Last,Repeats),
	rm_commutative(Last,Commutative),
	rm_symmetric(Last,Symmetric),
	rm_redundant(Last,Redundant),
	rm_uselesslits(Last,NotConnected),
	TotalLiterals is Last-Repeats-NotConnected-Commutative-Symmetric-Redundant,
	show(bottom),
	p1_message('literals'), p_message(TotalLiterals),
	p1_message('saturation time'), p_message(Time),
	store(bottom),
	noset(stage).
sat(_,_):-
	noset(stage).

reduce:-
	setting(search,Search), 
	catch(reduce(Search),abort,reinstate_values), !.

% iterative beam search as described by Ross Quinlan+MikeCameron-Jones,IJCAI-95
reduce(ibs):-
	!,
	retract_all(ibs),
	store_values([search,openlist,caching,explore]),
	set(search,bf),
	set(openlist,1),
	set(caching,true),
	set(explore,true),
	recorda(ibs,rval(1.0),_),
	recorda(ibs,nodes(0),_),
	recorded(sat,sat(Num,Type),_),
	example(Num,Type,Example),
	setting(evalfn,Evalfn),
	get_start_label(Evalfn,Label),
	recorda(ibs,selected(Label,(Example:-true),[Num-Num],[]),_),
	Start is cputime,
	repeat,
	setting(openlist,OldOpen),
	p1_message('ibs beam width'), p_message(OldOpen),
	reduce_clause,
	recorded(search,current(_,Nodes0,[PC,NC|_]/_),_),
	N is NC + PC,
	estimate_error_rate(Nodes0,0.5,N,NC,NewR),
	p1_message('ibs estimated error'), p_message(NewR),
	recorded(ibs,rval(OldR),DbRef1),
	recorded(ibs,nodes(Nodes1),DbRef2),
        recorded(search,selected(BL,RCl,PCov,NCov),_),
	erase(DbRef1),
	erase(DbRef2),
	NewOpen is 2*OldOpen,
	Nodes2 is Nodes0 + Nodes1,
	set(openlist,NewOpen),
	recorda(ibs,rval(NewR),_),
	recorda(ibs,nodes(Nodes2),_),
	((NewR >= OldR; NewOpen > 512) -> true;
		recorded(ibs,selected(_,_,_,_),DbRef3),
		erase(DbRef3),
		recorda(ibs,selected(BL,RCl,PCov,NCov),_),
		fail),
	!,
	Stop is cputime,
	Time is Stop - Start,
	recorded(ibs,nodes(Nodes),_),
        recorded(ibs,selected(BestLabel,RClause,PCover,NCover),_),
	add_hyp(BestLabel,RClause,PCover,NCover),
	p1_message('ibs clauses constructed'), p_message(Nodes),
	p1_message('ibs search time'), p_message(Time),
	p_message('ibs best clause'),
	pp_dclause(RClause),
	show_stats(Evalfn,BestLabel),
	record_search_stats(RClause,Nodes,Time),
	reinstate_values([search,openlist,caching,explore]).

% iterative language search as described by Rui Camacho, 1996
reduce(ils):-
	!,
	retract_all(ils),
	store_values([search,caching,language]),
	set(search,bf),
	set(language,1),
	set(caching,true),
	recorda(ils,nodes(0),_),
	recorded(sat,sat(Num,Type),_),
	example(Num,Type,Example),
	setting(evalfn,Evalfn),
	get_start_label(Evalfn,Label),
	recorda(ils,selected(Label,(Example:-true),[Num-Num],[]),_),
	Start is cputime,
	repeat,
	setting(language,OldLang),
	p1_message('ils language setting'), p_message(OldLang),
	reduce,
	recorded(search,current(_,Nodes0,_),_),
	recorded(ils,nodes(Nodes1),DbRef1),
        recorded(search,selected([P,N,L,F|T],RCl,PCov,NCov),_),
	recorded(ils,selected([_,_,_,F1|_],_,_,_),DbRef2),
	erase(DbRef1),
	NewLang is OldLang + 1,
	Nodes2 is Nodes0 + Nodes1,
	set(language,NewLang),
	recorda(ils,nodes(Nodes2),_),
	(F1 >= F -> true;
		erase(DbRef2),
		recorda(ils,selected([P,N,L,F|T],RCl,PCov,NCov),_),
		set(best,[P,N,L,F|T]),
		fail),
	!,
	Stop is cputime,
	Time is Stop - Start,
	recorded(ils,nodes(Nodes),_),
        recorded(ils,selected(BestLabel,RClause,PCover,NCover),_),
	add_hyp(BestLabel,RClause,PCover,NCover),
	p1_message('ils clauses constructed'), p_message(Nodes),
	p1_message('ils search time'), p_message(Time),
	p_message('ils best clause'),
	pp_dclause(RClause),
	show_stats(Evalfn,BestLabel),
	record_search_stats(RClause,Nodes,Time),
	noset(best),
	reinstate_values([search,caching,language]).


% implementation of a randomised local search for clauses
% currently, this can use either: simulated annealing with a fixed temp
% or a GSAT-like algorithm
% the choice of these is specified by the parameter: rls_type
% both annealing and GSAT employ random multiple restarts
% and a limit on the number of moves
%	the number of restarts is specified by set(tries,...)
%	the number of moves is specified by set(moves,...)
% annealing currently restricted to using a fixed temperature
%	the temperature is specified by set(temperature,...)
%	the use of a fixed temp. makes it equivalent to the Metropolis alg.
% GSAT if given a ``random-walk probability'' performs Selman et als walksat
%	the walk probability is specified by set(walk,...)
%	a walk probability of 0 is equivalent to doing standard GSAT
reduce(rls):-
	!,
	retract_all(rls),
	setting(tries,MaxTries),
	MaxTries >= 1,
	store_values([search,caching,refine,refineop]),
	set(search,heuristic),
	set(caching,true),
	set(refine,rls),
	set(refineop,true),
	setting(evalfn,Evalfn),
	get_start_label(Evalfn,Label),
	recorded(sat,sat(Num,Type),_),
	example(Num,Type,Example),
	recorda(rls,selected(Label,(Example:-true),[Num-Num],[]),_),
	recorda(rls,nodes(0),_),
	recorda(rls,restart(1),_),
	get_search_settings(S),
	set(best,Label),
	Start is cputime,
	repeat,
	retract_all(rls,parent_stats(_,_,_)),
	retract_all(rls,move(_)),
	retract_all(rls,seen(_)),
	recorda(rls,move(1),_),
	recorda(rls,parent_stats(Label,[],[]),_),
	recorded(rls,restart(R),DbRef0),
	p1_message('restart'), p_message(R),
	arg(4,S,Search/_),
	reduce(Search),
	recorded(search,current(_,Nodes0,_),_),
	recorded(rls,nodes(Nodes1),DbRef1),
        recorded(search,selected([P,N,L,F|T],RCl,PCov,NCov),_),
	recorded(rls,selected([_,_,_,F1|_],_,_,_),DbRef2),
	erase(DbRef0),
	R1 is R + 1,
	recorda(rls,restart(R1),_),
	erase(DbRef1),
	Nodes2 is Nodes0 + Nodes1,
	recorda(rls,nodes(Nodes2),_),
	(F1 >= F -> true;
		erase(DbRef2),
		recorda(rls,selected([P,N,L,F|T],RCl,PCov,NCov),_),
		set(best,[P,N,L,F|T])),
	setting(best,BestSoFar),
	(R1 > MaxTries;discontinue_search(S,BestSoFar/_,Nodes2)),
	!,
	Stop is cputime,
	Time is Stop - Start,
	recorded(rls,nodes(Nodes),_),
        recorded(rls,selected(BestLabel,RBest,PCover,NCover),_),
	add_hyp(BestLabel,RBest,PCover,NCover),
	p1_message('rls nodes constructed'), p_message(Nodes),
	p1_message('rls search time'), p_message(Time),
	p_message('rls best result'),
	pp_dclause(RBest),
	show_stats(Evalfn,BestLabel),
	record_search_stats(RBest,Nodes,Time),
	noset(best),
	reinstate_values([search,caching,refine,refineop]).

% stochastic clause selection based on ordinal optimisation
% see papers by Y.C. Ho and colleagues for more details
reduce(scs):-
	!,
	retract_all(scs),
	store_values([tries,moves,rls_type,clauselength_distribution]),
	Start is cputime,
	(setting(scs_sample,SampleSize) -> true;
		setting(scs_percentile,K),
		K > 0.0,
		setting(scs_prob,P),
		P < 1.0,
		SampleSize is integer(log(1-P)/log(1-K/100) + 1)),
	(setting(scs_type,informed)->
		(setting(clauselength_distribution,D) -> true;
			setting(clauselength,CL),
			estimate_clauselength_distribution(CL,100,K,D),
			% max_in_list(D,Prob-Length),
			% p1_message('using clauselength distribution'),
			% p_message([Prob-Length]),
			% set(clauselength_distribution,[Prob-Length]));
			p1_message('using clauselength distribution'),
			p_message(D),
			set(clauselength_distribution,D));
		true),
	set(tries,SampleSize),
	set(moves,0),
	set(rls_type,gsat),
	reduce(rls),
	Stop is cputime,
	Time is Stop - Start,
	recorded(rls,nodes(Nodes),_),
        recorded(rls,selected(BestLabel,RBest,_,_),_),
	p1_message('scs nodes constructed'), p_message(Nodes),
	p1_message('scs search time'), p_message(Time),
	p_message('scs best result'),
	pp_dclause(RBest),
	setting(evalfn,Evalfn),
	show_stats(Evalfn,BestLabel),
	record_search_stats(RBest,Nodes,Time),
	p1_message('scs search time'), p_message(Time),
	reinstate_values([tries,moves,rls_type,clauselength_distribution]).

% simple association rule search
% For a much more sophisticated approach see: L. DeHaspe, PhD Thesis, 1998
% Here, simply find all rules within search that cover at least
% a pre-specificed fraction of the positive examples
reduce(ar):-
	!,
	clear_cache,
	(setting(pos_fraction,PFrac) -> true;
		p_message('value required for pos_fraction parameter'),
		fail),
        recorded(aleph,atoms_left(pos,Pos),_),
	recorded(aleph,atoms_left(neg,Neg),DbRef),
	interval_count(Pos,P),
	MinPos is PFrac*P,
	store_values([search,minpos,evalfn,explore,caching,minacc]),
	set(search,bf),
	set(minpos,MinPos),
	set(evalfn,coverage),
	set(explore,true),
	set(caching,true),
	set(minacc,0.0),
	erase(DbRef),
	recorda(aleph,atoms_left(neg,[]),DbRef1),
	reduce,
	show(good),
	erase(DbRef1),
	recorda(aleph,atoms_left(neg,Neg),_),
	reinstate_values([search,minpos,evalfn,explore,caching,minacc]).

reduce(_):-
	set(stage,reduction),
	p_message('reduce'),
	reduce_prelims(L,P,N),
	recorda(openlist,[],_),
	get_search_settings(S),
	arg(4,S,_/Evalfn),
	get_start_label(Evalfn,Label),
	recorded(sat,sat(Num,Type),_),
	example(Num,Type,Example),
	recorda(search,selected(Label,(Example:-true),[Num-Num],[]),_),
	arg(13,S,MinPos),
	interval_count(P,PosLeft),
	PosLeft >= MinPos, !,
	add_hyp(Label,(Example:-true),[Num-Num],[]),
        (recorded(aleph,max_set(Type,Num,Label1,ClauseNum),_)->
		BestSoFar = Label1/ClauseNum;
		(recorded(aleph,set(best,Label2),_)->
			BestSoFar = Label2/0;
			BestSoFar = Label/0)),
        recorda(search,best_label(BestSoFar),_),
	p1_message('best label so far'), p_message(BestSoFar),
        arg(3,S,RefineOp),
	StartClock is cputime,
        (RefineOp = true ->
		clear_cache,
		interval_count(P,MaxPC),
		recorda(aleph_dyn,max_head_count(MaxPC),_),
		StartClause = 0-[Num,Type,[],false],
                get_gains(S,0,BestSoFar,StartClause,_,_,_,L,[StartClause],P,N,[],1,Last,NextBest);
                get_gains(S,0,BestSoFar,[],false,[],0,L,[1],P,N,[],1,Last,NextBest),
		update_max_head_count(0,Last)),
        recorda(search,expansion(1,0,1,Last),_),
	get_nextbest(S,_),
	recorda(search,current(1,Last,NextBest),_),
	search(S,Nodes),
	StopClock is cputime,
	Time is StopClock - StartClock,
        recorded(search,selected(BestLabel,RClause,PCover,NCover),_),
	recorded(openlist,_,DbRef),
	erase(DbRef),
	add_hyp(BestLabel,RClause,PCover,NCover),
	p1_message('clauses constructed'), p_message(Nodes),
	p1_message('search time'), p_message(Time),
	p_message('best clause'),
	pp_dclause(RClause),
	show_stats(Evalfn,BestLabel),
	update_search_stats(Nodes,Time),
	record_search_stats(RClause,Nodes,Time),
	noset(stage),
	!.
reduce(_):-
        recorded(search,selected(BestLabel,RClause,PCover,NCover),_),
	recorded(openlist,_,DbRef),
	erase(DbRef),
	add_hyp(BestLabel,RClause,PCover,NCover),
	p_message('best clause'),
	pp_dclause(RClause),
	(setting(evalfn,Evalfn) -> true; Evalfn = coverage),
	show_stats(Evalfn,BestLabel),
	noset(stage),
	!.

reduce_theory(Type):-
	!,
	retract_all(Type),
	(Type = rls ->
		setting(tries,MaxTries);
		MaxTries = 1),
	MaxTries >= 1,
	store_values([caching,refine,refineop,store_bottom]),
	set(caching,false),
	set(store_bottom,true),
	set(refine,Type),
	set(refineop,true),
        recorded(aleph,atoms(pos,PosSet),_),
        recorded(aleph,atoms(neg,NegSet),_),
        interval_count(PosSet,P0),
        interval_count(NegSet,N0),
	setting(evalfn,Evalfn),
        complete_label(Evalfn,[0-[0,0,[],false]],[P0,N0,1],Label),
	recorda(Type,selected(Label,[0-[0,0,[],false]],PosSet,NegSet),_),
	recorda(Type,nodes(0),_),
	recorda(Type,restart(1),_),
	get_search_settings(S),
	set(best,Label),
	Start is cputime,
	repeat,
	retract_all(Type,parent_stats(_,_,_)),
	retract_all(Type,move(_)),
	retract_all(Type,seen(_)),
	recorda(Type,move(1),_),
	recorda(Type,parent_stats(Label,PosSet,NegSet),_),
	recorded(Type,restart(R),DbRef0),
	p1_message('restart'), p_message(R),
	reduce_theory1(Type),
	recorded(search,current(_,Nodes0,_),_),
	recorded(Type,nodes(Nodes1),DbRef1),
        recorded(search,selected([P,N,L,F|T],RCl,PCov,NCov),_),
	recorded(Type,selected([_,_,_,F1|_],_,_,_),DbRef2),
	erase(DbRef0),
	R1 is R + 1,
	recorda(Type,restart(R1),_),
	erase(DbRef1),
	Nodes2 is Nodes0 + Nodes1,
	recorda(Type,nodes(Nodes2),_),
	(F1 >= F -> true;
		erase(DbRef2),
		recorda(Type,selected([P,N,L,F|T],RCl,PCov,NCov),_),
		set(best,[P,N,L,F|T])),
	setting(best,BestSoFar),
	(R1 > MaxTries;discontinue_search(S,BestSoFar/_,Nodes2)),
	!,
	Stop is cputime,
	Time is Stop - Start,
	recorded(Type,nodes(Nodes),_),
        recorded(Type,selected(BestLabel,RBest,PCover,NCover),_),
	add_hyp(BestLabel,RBest,PCover,NCover),
	p1_message('nodes constructed'), p_message(Nodes),
	p1_message('search time'), p_message(Time),
	p_message('best theory'),
	pp_dclauses(RBest),
	show_stats(Evalfn,BestLabel),
	record_search_stats(RBest,Nodes,Time),
	noset(best),
	reinstate_values([caching,refine,refineop,store_bottom]).

reduce_theory1(_):-
	clean_up_reduce,
	recorded(aleph,atoms(pos,Pos),_),
	recorded(aleph,atoms(neg,Neg),_),
        recorda(openlist,[],_),
	recorda(search,nextnode(none),_),
        record_settings,
        StartClock is cputime,
        get_search_settings(S),
	arg(4,S,_/Evalfn),
        interval_count(Pos,P),
        interval_count(Neg,N),
        complete_label(Evalfn,[0-[0,0,[],false]],[P,N,1],Label),
	recorda(search,selected(Label,[0-[0,0,[],false]],Pos,Neg),_),
	get_theory_gain(S,0,Label/0,[0-[0,0,[],false]],Pos,Neg,P,N,NextBest,Last),
	recorda(search,current(0,Last,NextBest),_),
	get_nextbest(S,_),
	tsearch(S,Nodes),
	StopClock is cputime,
	Time is StopClock - StartClock,
	recorded(search,selected(BestLabel,RTheory,PCover,NCover),_),
	recorded(openlist,_,DbRef),
	erase(DbRef),
	add_hyp(BestLabel,RTheory,PCover,NCover),
	p1_message('theories constructed'), p_message(Nodes),
	p1_message('search time'), p_message(Time),
	p_message('best theory'),
	pp_dclauses(RTheory),
	show_stats(Evalfn,BestLabel),
	update_search_stats(Nodes,Time),
	record_tsearch_stats(RTheory,Nodes,Time).

estimate_error_rate(H,Del,N,E,R):-
	TargetProb is 1-exp(log(1-Del)/H),
	estimate_error(1.0/0.0,0.0/1.0,TargetProb,N,E,R).

estimate_error(L/P1,U/P2,P,N,E,R):-
	M is (L+U)/2,
	binom_lte(N,M,E,P3),
	ADiff is abs(P - P3),
	(ADiff < 0.00001 ->
		R is M;
		(P3 > P ->
			estimate_error(L/P1,M/P3,P,N,E,R);
			estimate_error(M/P3,U/P2,P,N,E,R)
		)
	).
		

zap_rest(Lits):-
	recorded(lits,lit_info(LitNum,Depth,Atom,I,O,D),DbRef),
	erase(DbRef),
	(aleph_member1(LitNum,Lits) ->
		intersect1(Lits,D,D1,_),
		recorda(lits,lit_info(LitNum,Depth,Atom,I,O,D1),_);
		true),
	fail.
zap_rest(_).

sat_prelims:-
	clean_up_sat,
	clear_hyp,
	reset_counts,
	set_up_builtins.

reduce_prelims(L,P,N):-
	clean_up_reduce,
	check_posonly,
	check_auto_refine,
	(recorded(sat,last_lit(L),_)-> true;
		L = 0, recorda(sat,last_lit(L),_)),
	(recorded(sat,bot_size(B),_)-> true;
		B = 0, recorda(sat,bot_size(B),_)),
        ((recorded(aleph,lazy_evaluate(_),_);setting(greedy,true))->
                recorded(aleph,atoms_left(pos,P),_);
                recorded(aleph,atoms(pos,P),_)),
	set(evalfn,E),
	(E = posonly -> NType = rand; NType = neg),
	recorded(aleph,atoms_left(NType,N),_),
	recorda(search,nextnode(none),_).

set_up_builtins:-
	recorda(lits,lit_info(-1,0,'!',[],[],[]),_).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% C O N T R O L

% induce/0: the basic theory construction predicate
% constructs theories 1 clause at a time
% does greedy cover removal after each clause found
induce:-
	clean_up,
	set(greedy,true),
	retract_all(aleph,search_stats(_,_)),
        recorded(aleph,atoms_left(pos,PosSet),_),
        not(PosSet = []),
	store(portray_search),
	set(portray_search,false),
        setting(samplesize,S),
	record_settings,
        StartClock is cputime,
        repeat,
        gen_sample(pos,S),
	retract_all(aleph,besthyp(_,_,_,_,_)),
        recorda(aleph,besthyp([-10000,0,1,-10000],0,(false),[],[]),_),
        get_besthyp,
        (setting(gcws,true) -> sphyp, addgcws; rm_seeds),
        recorded(aleph,atoms_left(pos,[]),_),
        StopClock is cputime,
        Time is StopClock - StartClock,
        show(theory),
        record_theory(Time),
	noset(greedy),
	reinstate(portray_search),
        p1_message('time taken'), p_message(Time), 
	show_total_stats,
	record_total_stats, !.
induce.

% construct theories 1 clause at a time
% does not perform greedy cover removal after each clause found
% constructs unique ``maximum cover set'' solution
% 	by obtaining the best clause covering each example
% slow
induce_max:-
	clean_up,
	retract_all(aleph,search_stats(_,_)),
	recorded(aleph,atoms(pos,PosSet),_),
	PosSet \= [],
	store(portray_search),
	set(portray_search,false),
	record_settings,
	StartClock is cputime,
	set(maxcover,true),
	induce_max(PosSet),
	StopClock is cputime,
	Time is StopClock - StartClock,
	show(theory),
	record_theory(Time),
	noset(maxcover),
	reinstate(portray_search),
	reinstate(greedy),
	p1_message('time taken'), p_message(Time),
	show_total_stats,
	record_total_stats, !.
induce_max.

induce_max([]).
induce_max([Start-Finish|Intervals]):-
	recorda(aleph_dyn,counter(Start),_),
	induce_max1(Finish),
	induce_max(Intervals).

induce_max1(Finish):-
        recorded(aleph_dyn,counter(S),_),
        S =< Finish, !,
        repeat,
        recorded(aleph_dyn,counter(Start),DbRef),
        erase(DbRef),
        recorda(aleph,example_selected(pos,Start),DbRef1),
        sat(Start),
        reduce,
        update_coverset(pos,Start),
        erase(DbRef1),
        Next is Start+1,
        recordz(aleph_dyn,counter(Next),DbRef2),
        Next > Finish, !,
        erase(DbRef2).
induce_max1(_).

% construct theories 1 clause at a time
% does not perform greedy cover removal after each clause found
induce_cover:-
	clean_up,
	retract_all(aleph,search_stats(_,_)),
	recorded(aleph,atoms_left(pos,PosSet),_),
	not(PosSet = []),
	store(portray_search),
	set(portray_search,false),
	setting(samplesize,S),
	record_settings,
	StartClock is cputime,
        repeat,
	gen_sample(pos,S),
	recorda(aleph,besthyp([-10000,0,1,-10000],0,(false),[],[]),_),
	get_besthyp,
	rm_seeds,
        recorded(aleph,atoms_left(pos,[]),_),
	StopClock is cputime,
	Time is StopClock - StartClock,
        show(theory), 
	record_theory(Time),
	reinstate(portray_search),
	reinstate(greedy),
	p1_message('time taken'), p_message(Time), 
	show_total_stats,
	record_total_stats, !.
induce_cover.

% rudimentary version of an incremental learner
% repeatedly does the following:
%	1. ask the user for an example
%		default is to use a new positive example from previous search
%		if user responds with Ctrl-d (eof) then search stops
%		if user responds with "ok" then default is used
%		otherwise user has to provide an example
%	2. construct bottom clause using that example
%		expects to have appropriate mode declarations
%	3. search for the best clause C
%	4. ask the user about C who can respond with
%		ok: clause added to theory
%		prune: statement added to prevent future
%				clauses that are subsumed by C
%		overgeneral: constraint added to prevent future
%				clauses that subsume C
%		overgeneral because not E: E is added as a negative example
%		overspecific: C is added as new positive example
%		overspecific because E: E is added as a new positive example
%		X: where X is some aleph command like "covers"
%		Ctrl-d (eof): return to Step 1		
induce_incremental:-
	clean_up,
	retract_all(aleph,search_stats(_,_)),
	store(portray_search),
	set(portray_search,false),
	store(proof_strategy),
	set(proof_strategy,sld),
	record_settings,
        StartClock is cputime,
        repeat,
	ask_example(E),
	((E = end_of_file; E = none) -> true;
		once(record_example(check,pos,E,N)),
		retract_all(aleph,example_selected(_,_)),
        	recorda(aleph,example_selected(pos,N),_),
		once(sat(N)),
		once(reduce),
		once(process_hypothesis),
		fail),
	!,
        StopClock is cputime,
        Time is StopClock - StartClock,
        show(theory),
	show(pos),
	show(neg),
	show(constraints),
	show(prunes),
        record_theory(Time),
	reinstate(portray_search),
	reinstate(proof_strategy),
        p1_message('time taken'), p_message(Time).

% induce_theory/0: does theory-level search
% currently only with search = rls or mcmc; and evalfn = accuracy
induce_theory:-
	setting(search,Search),
	induce_theory(Search).

% induce entire theories from batch data
% using a randomised local search
% 	currently, this can use either: simulated annealing with a fixed temp,
% 	GSAT, or a WSAT-like algorithm
% 	the choice of these is specified by the parameter: rls_type
% 	all methods employ random multiple restarts
% 	and a limit on the number of moves
%       	the number of restarts is specified by set(tries,...)
%       	the number of moves is specified by set(moves,...)
% 	annealing currently restricted to using a fixed temperature
%       	the temperature is specified by set(temperature,...)
%       	the fixed temp. makes it equivalent to the Metropolis alg.
% 	WSAT requires a ``random-walk probability'' 
%       	the walk probability is specified by set(walk,...)
%       	a walk probability of 0 is equivalent to doing standard GSAT
% 	theory accuracy is the evaluation function
induce_theory(rls):-
	clean_up,
        retract_all(aleph,search_stats(_,_)),
        store(evalfn),
        set(evalfn,accuracy),
	reduce_theory(rls),
        reinstate(evalfn),
	show_total_stats,
	record_total_stats, !.

% induce entire theories from batch data
% using markov chain monte carlo
induce_theory(mcmc):-
	clean_up,
        retract_all(aleph,search_stats(_,_)),
        store(evalfn),
        set(evalfn,accuracy),
	reduce_theory(mcmc),
        reinstate(evalfn),
	show_total_stats,
	record_total_stats, !.

induce_theory(_).


% utilities for the induce predicates

% randomly pick a positive example and construct bottom clause
%	example is from those uncovered by current theory
%	and whose bottom clause has not been stored away previously
% 	makes at most 100 attempts to find such an example
rsat:-
        recorded(aleph,atoms_left(pos,PosSet),_),
        not(PosSet = []),
	rsat(100).

rsat(0):- !.
rsat(N):-
        gen_sample(pos,1),
	recorded(aleph,example_selected(pos,Num),DbRef),
	(not(recorded(bottom,stored(Num,pos,_),_)) ->
		!,
		erase(DbRef),
		sat(pos,Num);
		N1 is N - 1,
		rsat(N1)).

get_besthyp:-
	recorded(aleph,example_selected(pos,Num),DbRef),
	erase(DbRef),
	sat(Num),
	reset_best_label,	 % set-up target to beat
	reduce,
	update_besthyp(Num),
	fail.
get_besthyp:-
        recorded(aleph,besthyp(L,Num,H,PC,NC),DbRef),
        erase(DbRef),
	H \= false, !,
	((setting(samplesize,S),S>1)->
		setting(nodes,Nodes),
		show_clause(L,H,Nodes,sample),
		record_clause(L,H,Nodes,sample);
		true),
        add_hyp(L,H,PC,NC),
        recorda(aleph,example_selected(pos,Num),_), !.
get_besthyp.


reset_best_label:-
	recorded(aleph,besthyp(Label1,_,Clause,P,N),_),
	recorded(search,best_label(Label/_),DbRef),
	Label = [_,_,_,Gain|_],
	Label1 = [_,_,_,Gain1|_],
	Gain1 > Gain, !,
	erase(DbRef),
	recorda(search,best_label(Label1/0),_),
	recorded(search,selected(_,_,_,_),DbRef2),
	erase(DbRef2),
	recorda(search,selected(Label1,Clause,P,N),_).
reset_best_label.


update_besthyp(Num):-
	recorded(aleph,hypothesis(Label,H,PCover,NCover),_),
	recorded(aleph,besthyp(Label1,_,_,_,_),DbRef),
	Label = [_,_,_,Gain|_],
	Label1 = [_,_,_,Gain1|_],
	Gain > Gain1, !,
	erase(DbRef),
	recordz(aleph,besthyp(Label,Num,H,PCover,NCover),_).
update_besthyp(_).

ask_example(E):-
	(recorded(aleph,example_selected(pos,N),_) ->
		example(N,pos,E1);
		E1 = none),
	!,
	show_options(example_selection),
	tab(4),
	write('Response '), p1_message(default:E1), write('?'), nl,
	read(Response),
	(Response = ok  -> E = E1; E = Response).

process_hypothesis:-
	show(hypothesis),
	repeat,
	show_options(hypothesis_selection),
	tab(4),
	write('Response?'), nl,
	read(Response),
	process_hypothesis(Response),
	Response = end_of_file, !.


process_hypothesis(end_of_file):-
	nl, nl, !.
process_hypothesis(ok):-
	!,
	update_theory(_),
	nl, p_message('added new clause').
process_hypothesis(prune):-
        !,
        recorded(aleph,hypothesis(_,H,_,_),DbRef),
        erase(DbRef),
        Prune = (
                hypothesis(Head,Body,_),
                goals_to_list(Body,BodyL),
                clause_to_list(H,HL),
                aleph_subsumes(HL,[Head|BodyL])),
        assertz((prune(H):- Prune)),
        nl, p_message('added new prune statement').
process_hypothesis(overgeneral):-
        !,
        recorded(aleph,hypothesis(_,H,_,_),DbRef),
        erase(DbRef),
        Constraint = (
                hypothesis(Head,Body,_),
                goals_to_list(Body,BodyL),
                clause_to_list(H,HL),
                aleph_subsumes([Head|BodyL],HL)),
        assertz((false:- Constraint)),
        nl, p_message('added new constraint'). 
process_hypothesis(overgeneral because not E):-
	!,
	record_example(check,neg,E,_),
	nl, p_message('added new negative example').
process_hypothesis(overspecific):-
	!,
	recorded(aleph,hypothesis(_,H,_,_),DbRef),
	erase(DbRef),
	(recorded(aleph,example_selected(_,_),DbRef1)->
		erase(DbRef1);
		true),
	record_example(check,pos,H,N),
	recorda(aleph,example_selected(pos,N),_),
	nl, p_message('added new positive example').
process_hypothesis(overspecific because E):-
	!,
	recorded(aleph,hypothesis(_,_,_,_),DbRef),
	erase(DbRef),
	(recorded(aleph,example_selected(_,_),DbRef1)->
		erase(DbRef1);
		true),
	record_example(check,pos,E,N),
	recorda(aleph,example_selected(pos,N),_),
	nl, p_message('added new positive example').
process_hypothesis(AlephCommand):-
	AlephCommand.

show_options(example_selection):-
	nl,
	tab(4),
	write('Options:'), nl,
	tab(8),
	write('-> "ok." to accept default example'), nl,
	tab(8),
	write('-> Enter an example'), nl, 
	tab(8),
	write('-> ctrl-D or "none." to end'), nl, nl.
show_options(hypothesis_selection):-
	nl,
	tab(4),
	write('Options:'), nl,
	tab(8),
	write('-> "ok." to accept clause'), nl,
	tab(8),
        write('-> "prune." to prune clause and its refinements from the search'), nl,
        tab(8),
	write('-> "overgeneral." to add clause as a constraint'), nl, 
	tab(8),
	write('-> "overgeneral because not E." to add E as a negative example'), nl, 
	tab(8),
	write('-> "overspecific." to add clause as a positive example'), nl, 
	tab(8),
	write('-> "overspecific because E." to add E as a positive xample'), nl, 
	tab(8),
	write('-> any Aleph command'), nl, 
	tab(8),
	write('-> ctrl-D to end'), nl, nl.
	

get_performance:-
	(setting(train_pos,PFile) ->
		test(PFile,noshow,Tp,TotPos),
		Fn is TotPos - Tp;
		TotPos = 0, Tp = 0, Fn = 0),
	(setting(train_neg,NFile) ->
		test(NFile,noshow,Fp,TotNeg),
		Tn is TotNeg - Fp;
		TotNeg = 0, Tn = 0, Fp = 0),
	TotPos + TotNeg > 0,
	p_message('Training set performance'),
	write_cmatrix([Tp,Fp,Fn,Tn]),
	p1_message('Training set summary'), p_message([Tp,Fp,Fn,Tn]),
	fail.
get_performance:-
	(setting(test_pos,PFile) ->
		test(PFile,noshow,Tp,TotPos),
		Fn is TotPos - Tp;
		TotPos = 0, Tp = 0, Fn = 0),
	(setting(test_neg,NFile) ->
		test(NFile,noshow,Fp,TotNeg),
		Tn is TotNeg - Fp;
		TotNeg = 0, Tn = 0, Fp = 0),
	TotPos + TotNeg > 0,
	p_message('Test set performance'),
	write_cmatrix([Tp,Fp,Fn,Tn]),
	p1_message('Test set summary'), p_message([Tp,Fp,Fn,Tn]),
	fail.
get_performance.

write_cmatrix([Tp,Fp,Fn,Tn]):-
        P is Tp + Fn, N is Fp + Tn,
        PP is Tp + Fp, PN is Fn + Tn,
        Total is PP + PN,
        (Total = 0 -> Accuracy is 0.5; Accuracy is (Tp + Tn)/Total),
        find_max_width([Tp,Fp,Fn,Tn,P,N,PP,PN,Total],0,W1),
        W is W1 + 2,
        tab(5), write(' '), tab(W), write('Actual'), nl,
        tab(5), write(' '), write_entry(W,'+'), tab(6), write_entry(W,'-'), nl,
        tab(5), write('+'),
        write_entry(W,Tp), tab(6), write_entry(W,Fp), tab(6), write_entry(W,PP), nl,
        write('Pred '), nl,
        tab(5), write('-'),
        write_entry(W,Fn), tab(6), write_entry(W,Tn), tab(6), write_entry(W,PN), nl, nl,
        tab(5), write(' '), write_entry(W,P), tab(6), write_entry(W,N),
        tab(6), write_entry(W,Total), nl, nl,
        write('Accuracy = '), write(Accuracy), nl.

 
find_max_width([],W,W).
find_max_width([V|T],W1,W):-
        name(V,VList),
        length(VList,VL),
        (VL > W1 -> find_max_width(T,VL,W);
                find_max_width(T,W1,W)).
 
write_entry(W,V):-
        name(V,VList),
        length(VList,VL),
        Y is integer((W-VL)/2),
        tab(Y), write(V), tab(Y).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% L A Z Y  E V A L U A T I O N


% lazy_evaluate_theory(+Clauses,+Lazy,+Pos,+Neg,-Theory)
%       evaluate lazy preds in a set of clauses
lazy_evaluate_theory([],_,_,_,[]).
lazy_evaluate_theory([Refine|T],LazyPreds,Pos,Neg,[Refine1|T1]):-
	Refine = A-[B,C,D,Clause],
        lazy_evaluate_refinement(Clause,LazyPreds,Pos,Neg,Clause1),
	Refine1 = A-[B,C,D,Clause1],
        lazy_evaluate_theory(T,LazyPreds,Pos,Neg,T1).

% lazy evaluation of literals in a refinement operation
lazy_evaluate_refinement(Refinement,LazyPreds,PosCover,NegCover,NewRefinement):-
	clause_to_list(Refinement,Lits),
	lazy_evaluate_refinement(Lits,LazyPreds,[],PosCover,NegCover,Lits1),
	list_to_clause(Lits1,NewRefinement), !.
lazy_evaluate_refinement(Refinement,_,_,_,Refinement).


lazy_evaluate_refinement([],_,L,_,_,L):- !.
lazy_evaluate_refinement([Lit|Lits],LazyPreds,Path,PosCover,NegCover,Refine):-
	lazy_evaluate([Lit],LazyPreds,Path,PosCover,NegCover,[Lit1]), 
	update(Path,Lit1,Path1), !,
	lazy_evaluate_refinement(Lits,LazyPreds,Path1,PosCover,NegCover,Refine).


% lazy evaluation of specified literals
% all #'d arguments of these literals are evaluated at reduction-time
lazy_evaluate(Lits,[],_,_,_,Lits):- !.
lazy_evaluate([],_,_,_,_,[]):- !.
lazy_evaluate([LitNum|LitNums],LazyPreds,Path,PosCover,NegCover,Lits):-
	(integer(LitNum) ->
		recorded(lits,lit_info(LitNum,Depth,Atom,I,O,D),_),
		functor(Atom,Name,Arity),
		aleph_member1(Name/Arity,LazyPreds), !,
		get_pclause([LitNum|Path],[],(Lit:-(Goals)),_,_,_);
		functor(LitNum,Name,Arity),
		aleph_member1(Name/Arity,LazyPreds), !,
		list_to_clause([LitNum|Path],(Lit:-(Goals)))),
	goals_to_clause(Goals,Clause),
	lazy_prove(pos,Lit,Clause,PosCover),
	(recorded(aleph,positive_only(Name/Arity),_)->
		lazy_prove(neg,Lit,Clause,[]);
		lazy_prove_negs(Lit,Clause,NegCover)),
	functor(LazyLiteral,Name,Arity),
	collect_args(I,LazyLiteral),
	lazy_evaluate1(Atom,Depth,I,O,D,LazyLiteral,NewLits),
	retract_all(aleph_dyn,lazy_evaluate(_,_)),
	lazy_evaluate(LitNums,LazyPreds,Path,PosCover,NegCover,NewLits1),
	update_list(NewLits1,NewLits,Lits).
lazy_evaluate([LitNum|LitNums],LazyPreds,Path,PosCover,NegCover,[LitNum|Lits]):-
	lazy_evaluate(LitNums,LazyPreds,Path,PosCover,NegCover,Lits).

lazy_prove_negs(Lit,Clause,_):-
	recorded(aleph,set(lazy_negs,true),_), !,
	recorded(aleph,atoms(neg,NegCover),_),
	lazy_prove(neg,Lit,Clause,NegCover).
lazy_prove_negs(Lit,Clause,NegCover):-
	lazy_prove(neg,Lit,Clause,NegCover).

collect_args([],_).
collect_args([Argno/_|Args],Literal):-
	findall(Term,(recorded(aleph_dyn,lazy_evaluate(pos,Lit),_),tparg(Argno,Lit,Term)),PTerms),
	findall(Term,(recorded(aleph_dyn,lazy_evaluate(neg,Lit),_),tparg(Argno,Lit,Term)),NTerms),
	tparg(Argno,Literal,[PTerms,NTerms]),
	collect_args(Args,Literal).

lazy_evaluate1(Atom,Depth,I,O,D,Lit,NewLits):-
	recorded(sat,last_lit(_),_),
	call_library_pred(Atom,Depth,Lit,I,O,D),
	findall(LitNum,(recorded(aleph_dyn,lazy_evaluated(LitNum),DbRef),erase(DbRef)),NewLits).

call_library_pred(OldLit,Depth,Lit,I,O,D):-
	functor(OldLit,Name,Arity),
	recorded(aleph,lazy_recall(Name/Arity,Recall),_),
	recorda(aleph_dyn,callno(1),_),
	p1_message('lazy evaluation'), p_message(Name),
	repeat,
	evaluate(OldLit,Depth,Lit,I,O,D),
	recorded(aleph_dyn,callno(CallNo),DbRef),
	erase(DbRef),
	NextCall is CallNo + 1,
	recorda(aleph_dyn,callno(NextCall),DbRef1),
	NextCall > Recall,
	!,
	p_message('completed'),
	erase(DbRef1).
	 
evaluate(OldLit,_,Lit,I,O,D):-
	functor(OldLit,Name,Arity),
	functor(NewLit,Name,Arity),
	Lit,
	copy_args(OldLit,NewLit,I),
	copy_args(OldLit,NewLit,O),
	copy_consts(Lit,NewLit,Arity),
	update_lit(LitNum,false,NewLit,I,O,D),
	not(recorded(aleph_dyn,lazy_evaluated(LitNum),_)),
	recorda(aleph_dyn,lazy_evaluated(LitNum),_), !.
evaluate(_,_,_,_,_,_).

copy_args(_,_,[]).
copy_args(Old,New,[Arg/_|T]):-
	tparg(Arg,Old,Term),
	tparg(Arg,New,Term),
	copy_args(Old,New,T), !.

copy_consts(_,_,0):- !.
copy_consts(Old,New,Arg):-
	arg(Arg,Old,Term),
	arg(Arg,New,Term1),
	var(Term1), !,
	Term1 = aleph_const(Term),
	Arg0 is Arg - 1,
	copy_consts(Old,New,Arg0).
copy_consts(Old,New,Arg):-
	Arg0 is Arg - 1,
	copy_consts(Old,New,Arg0).

% copy_modeterm(+Old,-New)
%	copy term structure from Old to New
%	by finding an appropriate mode declaration
copy_modeterm(Lit1,Lit2):-
	functor(Lit1,Name,Arity),
	functor(Mode,Name,Arity),
	recorded(aleph,mode(_,Mode),_),
	functor(Lit2,Name,Arity),
	copy_modeterms(Mode,Lit2,Arity),
	\+((\+ (Lit1 = Lit2))).

% copy_modeterms(+Mode,+Lit,+Arity)
% 	copy all term structures in a mode template
copy_modeterms(_,_,0):- !.
copy_modeterms(Mode,Lit,Arg):-
        arg(Arg,Mode,Term),
        functor(Term,Name,Arity),
        not((Name = '+'; Name = '-'; Name = '#')), !,
        functor(NewTerm,Name,Arity),
        arg(Arg,Lit,NewTerm),
        copy_modeterms(Term,NewTerm,Arity),
        Arg0 is Arg - 1,
        copy_modeterms(Mode,Lit,Arg0).
copy_modeterms(Mode,Lit,Arg):-
        Arg0 is Arg - 1,
        copy_modeterms(Mode,Lit,Arg0).


% theorem-prover for lazy evaluation of literals
lazy_prove(_,_,_,[]).
lazy_prove(Type,Lit,Clause,[Interval|Intervals]):-
        lazy_index_prove(Type,Lit,Clause,Interval),
        lazy_prove(Type,Lit,Clause,Intervals).

lazy_index_prove(_,_,_,Start-Finish):-
        Start > Finish, !.
lazy_index_prove(Type,Lit,Clause,Start-Finish):-
        lazy_index_prove1(Type,Lit,Clause,Start),
        Start1 is Start + 1,
        lazy_index_prove(Type,Lit,Clause,Start1-Finish).

% bind input args of lazy literal
% each example gives an set of input bindings
% this is different from Aleph 2 where only a single binding was obtained
lazy_index_prove1(Type,Lit,Clause,Num):-
        (Clause = (Head:-Body)->true;Head=Clause,Body=true),
        depth_bound_call((example(Num,Type,Head),Body)),
	not(recorded(aleph_dyn,lazy_evaluate(Type,Lit),_)),
        recorda(aleph_dyn,lazy_evaluate(Type,Lit),_),
        fail.
lazy_index_prove1(_,_,_,_).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% S L P
% implemented as described by Muggleton, ILP-96

condition_target:-
	recorded(aleph,set(condition,true),_),
	add_generator,
	recorded(aleph,modeh(_,Pred),_),
	functor(Pred,Name,Arity),
	p_message('conditioning'),
	make_sname(Name,SName),
	functor(SPred,SName,Arity),
	SPred =.. [_|Args],
	functor(Fact,Name,Arity),
	example(_,_,Fact),
	Fact =.. [_|Args], 
	condition(SPred),
	fail.
condition_target:-
	not(recorded(aleph,set(condition,true),_)),
	add_generator, !.
condition_target.


add_generator:-
	recorded(aleph,modeh(_,Pred),_),
	functor(Pred,Name,Arity),
	make_sname(Name,SName),
	functor(SPred,SName,Arity),
	(clause(SPred,_)-> 
		true;
		add_generator(Name/Arity),
		p1_message('included generator'), p_message(SName/Arity)).

add_generator(Name/Arity):-
	functor(Mode,Name,Arity),
	make_sname(Name,SName),
	functor(SPred,SName,Arity),
	recorded(aleph,modeh(_,Mode),_),
	once(copy_modeterms(Mode,SPred,Arity)),
	split_args(Mode,Mode,Input,Output,Constants),
	range_restrict(Input,SPred,[],B1),
	range_restrict(Output,SPred,B1,B2),
	range_restrict(Constants,SPred,B2,B3),
	list_to_goals(B3,Body),
	not(clause(SPred,Body)),
	asserta((SPred:-Body)),
	fail.
add_generator(_).

make_sname(Name,SName):-
	concat(['*',Name],SName).

range_restrict([],_,R,R).
range_restrict([Pos/Type|T],Pred,R0,R):-
	functor(TCheck,Type,1),
	tparg(Pos,Pred,X),
	arg(1,TCheck,X),
	range_restrict(T,Pred,[TCheck|R0],R).


condition(Fact):-
	slprove(condition,Fact), !.
condition(_).

sample(_,0,[]):- !.
sample(Name/Arity,N,S):-
	functor(Pred,Name,Arity),
	retract_all(slp,samplenum(_)),
	retract_all(slp,sample(_)),
	recorda(slp,samplenum(1),_),
	repeat,
	slprove(stochastic,Pred),
	recorda(slp,sample(Pred),_),
	recorded(slp,samplenum(N1),DbRef),
	erase(DbRef),
	N2 is N1 + 1,
	recorda(slp,samplenum(N2),DbRef1),
	N2 > N,
	!,
	erase(DbRef1),
	functor(Fact,Name,Arity),
	findall(Fact,(recorded(slp,sample(Fact),DbRef2),erase(DbRef2)),S).

gsample(Name/Arity,_):-
        make_sname(Name,SName),
        functor(SPred,SName,Arity),
        clause(SPred,true),
        ground(SPred), !,
        update_gsample(Name/Arity,_).
gsample(_,0):- !.
gsample(Name/Arity,N):-
	functor(Pred,Name,Arity),
	make_sname(Name,SName),
	functor(SPred,SName,Arity),
	Pred =.. [_|Args],
	retract_all(slp,samplenum(_)),
	recorda(slp,samplenum(0),_),
	repeat,
	slprove(stochastic,SPred),
	SPred =..[_|Args],
	recorded(slp,samplenum(N1),DbRef),
	erase(DbRef),
	N2 is N1 + 1,
	recorda(slp,samplenum(N2),DbRef1),
	assertz(example(N2,rand,Pred)),
	N2 >= N,
	!,
	erase(DbRef1),
	recorda(aleph,size(rand,N),_),
	recorda(aleph,last_example(rand,N),_),
	recorda(aleph,atoms(rand,[1-N]),_),
	recorda(aleph,atoms_left(rand,[1-N]),_).

update_gsample(Name/Arity,_):-
        functor(Pred,Name,Arity),
        make_sname(Name,SName),
        functor(SPred,SName,Arity),
        retract_all(aleph,gsample(_)),
        retract_all(slp,samplenum(_)),
        recorda(slp,samplenum(0),_),
        SPred =.. [_|Args],
        Pred =.. [_|Args],
        clause(SPred,true),
        ground(SPred),
        recorded(slp,samplenum(N1),DbRef),
        erase(DbRef),
        N2 is N1 + 1,
        recorda(slp,samplenum(N2),_),
        assertz(example(N2,rand,Pred)),
        fail.
update_gsample(_,N):-
        recorded(slp,samplenum(N),DbRef),
        N > 0, !,
        erase(DbRef),
        set(gsamplesize,N),
	recorda(aleph,size(rand,N),_),
	recorda(aleph,last_example(rand,N),_),
	recorda(aleph,atoms(rand,[1-N]),_),
	recorda(aleph,atoms_left(rand,[1-N]),_).
update_gsample(_,_).

	
slprove(_,true):-
	!.
slprove(Mode,not(Goal)):-
	slprove(Mode,Goal),
	!,
	fail.
slprove(Mode,(Goal1,Goal2)):-
	!,
	slprove(Mode,Goal1),
	slprove(Mode,Goal2).
slprove(Mode,(Goal1;Goal2)):-
	!,
	slprove(Mode,Goal1);
	slprove(Mode,Goal2).
slprove(_,Goal):-
	functor(Goal,Name,Arity),
	functor(BuiltIn,Name,Arity),
	system_predicate(Name,BuiltIn), !,
	Goal.
slprove(stochastic,Goal):-
	findall(Count/Clause,
		(clause(Goal,Body),Clause=(Goal:-Body),find_count(Clause,Count)),
		ClauseCounts),
	renormalise(ClauseCounts,Normalised),
	X is random,
	rselect_clause(X,Normalised,(Goal:-Body)),
	slprove(stochastic,Body).
slprove(condition,Goal):-
	functor(Goal,Name,Arity),
	functor(Head,Name,Arity),
	clause(Head,Body),
	not(not((Head=Goal,slprove(condition,Body)))),
	inc_count((Head:-Body)).

renormalise(ClauseCounts,Normalised):-
	sum_counts(ClauseCounts,L),
	L > 0,
	renormalise(ClauseCounts,L,Normalised).

sum_counts([],0).
sum_counts([N/_|T],C):-
	sum_counts(T,C1),
	C is N + C1.

renormalise([],_,[]).
renormalise([Count/Clause|T],L,[Prob/Clause|T1]):-
	Prob is Count/L,
	renormalise(T,L,T1).

rselect_clause(X,[P/C|_],C):- X =< P, !.
rselect_clause(X,[P/_|T],C):-
	X1 is X - P,
	rselect_clause(X1,T,C).


find_count(Clause,N):-
	copy_term(Clause,Clause1),
	recorded(slp,count(Clause1,N),_), !.
find_count(_,1).
	
inc_count(Clause):-
	recorded(slp,count(Clause,N),DbRef), !,
	erase(DbRef),
	N1 is N + 1,
	recorda(slp,count(Clause,N1),_).
inc_count(Clause):-
	recorda(slp,count(Clause,2),_).

find_posgain(PCover,P):-
	recorded(aleph,set(greedy,true),_), !,
	interval_count(PCover,P).
find_posgain(PCover,P):-
	recorded(aleph,atoms_left(pos,PLeft),_),
	intervals_intersection(PLeft,PCover,PC),
	interval_count(PC,P).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% S E A R C H  I / O 

record_clause(Label,Clause,Nodes,Flag):-
	recorded(aleph,set(record,true),_),
	recorded(aleph,set(recordfile,File),_), !,
	open(File,append,Stream),
	set_output(Stream),
	show_clause(Label,Clause,Nodes,Flag),
	close(Stream),
	set_output(user_output).
record_clause(_,_,_,_).

record_theory(Label,Clauses,Nodes,Flag):-
        recorded(aleph,set(record,true),_),
        recorded(aleph,set(recordfile,File),_), !,
        open(File,append,Stream),
        set_output(Stream),
        show_theory(Label,Clauses,Nodes,Flag),
        close(Stream),
        set_output(user_output).
record_theory(_,_,_,_).



record_sat_example(N):-
	recorded(aleph,set(record,true),_),
	recorded(aleph,set(recordfile,File),_), !,
	open(File,append,Stream),
	set_output(Stream),
	p1_message('sat'), p_message(N),
	close(Stream),
	set_output(user_output).
record_sat_example(_).


record_search_stats(Clause,Nodes,Time):-
	recorded(aleph,set(record,true),_),
	recorded(aleph,set(recordfile,File),_), !,
	open(File,append,Stream),
	set_output(Stream),
	p1_message('clauses constructed'), p_message(Nodes),
	p1_message('search time'), p_message(Time),
	p_message('best clause'),
	pp_dclause(Clause),
	% show(hypothesis),
	close(Stream),
	set_output(user_output).
record_search_stats(_,_,_).

record_tsearch_stats(Theory,Nodes,Time):-
        recorded(aleph,set(record,true),_),
        recorded(aleph,set(recordfile,File),_), !,
        open(File,append,Stream),
        set_output(Stream),
        p1_message('theories constructed'), p_message(Nodes),
        p1_message('search time'), p_message(Time),
        p_message('best theory'),
        pp_dclauses(Theory),
        % show(hypothesis),
        close(Stream),
        set_output(user_output).
record_tsearch_stats(_,_,_).



record_theory(Time):-
        recorded(aleph,set(record,true),_),
        recorded(aleph,set(recordfile,File),_), !,
        open(File,append,Stream),
        set_output(Stream),
        show(theory),
	p1_message('time taken'), p_message(Time),
        nl,
        (recorded(aleph,set(maxcover,true),_)->
                show(aleph,theory/5), nl,
                show(aleph,max_set/4), nl,
                show(aleph,rules/1);
                true),
        close(Stream),
        set_output(user_output).
record_theory(_).

record_settings:-
        recorded(aleph,set(record,true),_),
        recorded(aleph,set(recordfile,File),_), !,
	% record_date(File),
	% record_machine(File),
        open(File,append,Stream),
        set_output(Stream),
	show(settings),
	close(Stream),
        set_output(user_output).
record_settings.

% Unix specific date command
record_date(File):-
	concat([date,' >> ', File],Cmd),
	execute(Cmd).

% Unix specific machine name
record_machine(File):-
	concat([hostname,' >> ', File],Cmd),
	execute(Cmd).

show_clause(Label,Clause,Nodes,Flag):-
	p_message('-------------------------------------'),
	(Flag=good -> p_message('good clause');
		(Flag=sample-> p_message('selected from sample');
			p_message('found clause'))),
	pp_dclause(Clause),
	(setting(evalfn,Evalfn)-> true; Evalfn = coverage),
	show_stats(Evalfn,Label),
	p1_message('clause label'), p_message(Label),
	p1_message('clauses constructed'), p_message(Nodes),
	p_message('-------------------------------------').

show_theory(Label,Clauses,Nodes,Flag):-
        p_message('-------------------------------------'),
        (Flag=good -> p_message('good theory');
                (Flag=sample-> p_message('selected from sample');
                        p_message('found theory'))),
        pp_dclauses(Clauses),
        (setting(evalfn,Evalfn)-> true; Evalfn = accuracy),
        show_stats(Evalfn,Label),
        p1_message('theory label'), p_message(Label),
        p1_message('theories constructed'), p_message(Nodes),
        p_message('-------------------------------------').

update_search_stats(N,T):-
	(recorded(aleph,search_stats(N0,T0),DbRef) ->
			erase(DbRef),
			N1 is N0 + N,
			T1 is T0 + T;
			N1 is N,
			T1 is T),
	recorda(aleph,search_stats(N1,T1),_).

record_total_stats:-
	recorded(aleph,set(record,true),_),
	recorded(aleph,set(recordfile,File),_), !,
	open(File,append,Stream),
	set_output(Stream),
	show_total_stats,
	close(Stream),
	set_output(user_output).
record_total_stats.

show_total_stats:-
	recorded(aleph,search_stats(Nodes,_),_), !,
	p1_message('total clauses constructed'), p_message(Nodes).
show_total_stats.
	
	
show_stats(Evalfn,[_,_,_,F|_]):-
	print_eval(Evalfn,F).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% A U T O  -- R E F I N E
% 
% built-in refinement operator

gen_auto_refine:-
	(setting(autorefine,true) -> true;
		set(autorefine,true),
		process_modes,
		process_determs),
	!.
gen_auto_refine.

process_modes:-
	once(abolish(aleph_link_vars,2)),
	once(abolish(aleph_has_ovar,4)),
	once(abolish(aleph_has_ivar,4)),
	recorded(aleph,modeb(_,Mode),_),
	process_mode(Mode),
	fail.
process_modes:-
	recorded(aleph,determination(Name/Arity,_),_),
	functor(Mode,Name,Arity),
	recorded(aleph,modeh(_,Mode),_),
	split_args(Mode,Mode,I,O,_),
	functor(Lit,Name,Arity),
	copy_modeterms(Mode,Lit,Arity),
	add_ivars(Lit,I),
	add_ovars(Lit,O),
	fail.
process_modes.

process_determs:-
	once(abolish(aleph_determination,2)),
	recorded(aleph,determination(Name/Arity,Name1/Arity1),_),
	functor(Pred,Name1,Arity1),
	functor(Mode,Name1,Arity1),
	recorded(aleph,modeb(_,Mode),_),
	copy_modeterms(Mode,Pred,Arity1),
	Determ = aleph_determination(Name/Arity,Pred),
	(Determ -> true; assert_static(Determ)),
	fail.
process_determs.

process_mode(Mode):-
	functor(Mode,Name,Arity),
	split_args(Mode,Mode,I,O,C),
	functor(Lit,Name,Arity),
	copy_modeterms(Mode,Lit,Arity),
	add_ioc_links(Lit,I,O,C),
	add_ovars(Lit,O).

add_ioc_links(Lit,I,O,C):-
	Clause = (aleph_link_vars(Lit,Lits):-
			Body),
	get_o_links(O,Lit,Lits,true,OGoals),
	get_i_links(I,Lit,Lits,OGoals,IOGoals),
	get_c_links(C,Lit,IOGoals,Body),
	assert_static(Clause).

add_ovars(Lit,O):-
	aleph_member(Pos/Type,O),
	tparg(Pos,Lit,V),
	(aleph_has_ovar(Lit,V,Type,Pos)->true;
		assert_static(aleph_has_ovar(Lit,V,Type,Pos))),
	fail.
add_ovars(_,_).

add_ivars(Lit,I):-
	aleph_member(Pos/Type,I),
	tparg(Pos,Lit,V),
	(aleph_has_ivar(Lit,V,Type,Pos)->true;
		assert_static(aleph_has_ivar(Lit,V,Type,Pos))),
	fail.
add_ivars(_,_).


get_o_links([],_,_,Goals,Goals).
get_o_links([Pos/Type|T],Lit,Lits,GoalsSoFar,Goals):-
	tparg(Pos,Lit,V),
	Goal = (aleph_output_var(V,Type,Lits);
		aleph_output_var(V,Type,Lit,Pos)),
	prefix_lits((Goal),GoalsSoFar,G1),
	get_o_links(T,Lit,Lits,G1,Goals).


get_i_links([],_,_,Goals,Goals).
get_i_links([Pos/Type|T],Lit,Lits,GoalsSoFar,Goals):-
	tparg(Pos,Lit,V),
	Goal = aleph_input_var(V,Type,Lits),
	prefix_lits((Goal),GoalsSoFar,G1),
	get_i_links(T,Lit,Lits,G1,Goals).

get_c_links([],_,Goals,Goals).
get_c_links([Pos/Type|T],Lit,GoalsSoFar,Goals):-
	tparg(Pos,Lit,V),
	TypeFact =.. [Type,C],
	Goal = (TypeFact,V=C),
	prefix_lits((Goal),GoalsSoFar,G1),
	get_c_links(T,Lit,G1,Goals).
	

aleph_input_var(Var,Type,[Head|_]):-
	aleph_has_ivar(Head,Var,Type,_).
aleph_input_var(Var,Type,[_|Lits]):-
        aleph_member(Lit,Lits),
        aleph_has_ovar(Lit,Var,Type,_).

aleph_output_var(Var,Type,[Head|_]):-
	aleph_has_ovar(Head,Var,Type,_).
aleph_output_var(Var,Type,Lits):-
	aleph_input_var(Var,Type,Lits).
aleph_output_var(_,_,_).

aleph_output_var(Var,Type,Lit,ThisPos):-
	aleph_has_ovar(Lit,Var,Type,Pos),
	Pos @< ThisPos.

aleph_get_hlit(Name/Arity,Head):-
	functor(Head,Name,Arity),
	functor(Mode,Name,Arity),
	recorded(aleph,modeh(_,Mode),_),
	once(split_args(Mode,Mode,_,_,C)),
	copy_modeterms(Mode,Head,Arity),
	get_c_links(C,Head,true,Equalities),
	Equalities.

aleph_get_lit(Lit,[H|Lits]):-
	functor(H,Name,Arity),
	aleph_get_lit(Lit,Name/Arity),
	aleph_link_vars(Lit,[H|Lits]),
	not(aleph_member2(Lit,[H|Lits])).

aleph_get_lit(Lit,Target):-
	aleph_determination(Target,Lit).

% aleph_mode_linked(+Lits)
% checks to see if a sequence of literals are within mode language
% using information compiled by process_modes/0
aleph_mode_linked([H|B]):-
	aleph_mode_linked(B,[H]).

aleph_mode_linked([],_):- !.
aleph_mode_linked([Lit|Lits],LitsSoFar):-
	aleph_link_vars(Lit,LitsSoFar),
	aleph_append([Lit],LitsSoFar,L1),
	aleph_mode_linked(Lits,L1).

auto_refine(false,Head):-
        !,
        once(recorded(aleph,determination(Name/Arity,_),_)),
        aleph_get_hlit(Name/Arity,Head).
auto_refine((H:-B),(H1:-B1)):-
        !,
        goals_to_list((H,B),LitList),
        set(clauselength,L),
        length(LitList,ClauseLength),
        ClauseLength < L,
        aleph_get_lit(Lit,LitList),
        aleph_append([Lit],LitList,LitList1),
        list_to_goals(LitList1,(H1,B1)),
	not(prune((H1:-B1))).
auto_refine(Head,Clause):-
        auto_refine((Head:-true),Clause).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% S T O C H A S T I C   S E A R C H
 
% sample_clauses(+N,-Clauses)
%	return sample of at most N legal clauses from hypothesis space
%	If a bottom clause exists then
%		Each clause is drawn randomly. The length of the clause is
%		determined by:
%			(a) user-specified distribution over clauselengths
%			    using set(clauselength_distribution,Distribution);
%			    Distribution is a list of the form p1-1, p2-2,...
%			    specifying that clauselength 1 has prob p1, etc.
%			    Note: sum pi must = 1. This is not checked; or
%			(b) uniform distribution over all legal clauses.
%			    (if clauselength_distribution is not set)
%			    this uses a Monte-Carlo estimate of the number of
%			    legal clauses in the hypothesis space
%	If a bottom clause does not exist, then legal clauses are constructed
%	using the mode declarations. Only option (a) is allowed. If
%	clauselength_distribution is not set, then a uniform distribution over
%	lengths is assumed.
%	Each element of Clauses is of the form L-[E,T,Lits,Clause] where
%	L is the clauselength; E,T are example number and type (pos, neg) used
%	to build the bottom clause; Lits contains the literal numbers in the
%	bottom clause for Clause. If no bottom clause then E,T = 0 and Lits = []
% 	Clauses is in ascending order of clause length
sample_clauses(N,Clauses):-
	setting(construct_bottom,Bottom),
	sample_nclauses(Bottom,N,Clauses).

sample_nclauses(false,N,Clauses):-
	!,
	gen_auto_refine,
	(setting(clauselength_distribution,D) -> true;
		setting(clauselength,CL),
		Uniform is 1.0/CL,
		distrib(1-CL,Uniform,D)),
	sample_nclauses_using_modes(N,D,CList),
	remove_alpha_variants(CList,CList1),
	keysort(CList1,Clauses).
sample_nclauses(_,N,Clauses):-
	(recorded(sat,sat(_,_),_) -> true; rsat),
	retract_all(random,rselect(_)),
	setting(clauselength,CL),
	(setting(clauselength_distribution,Universe) ->
		Sample is N;
		estimate_numbers(CL,1,400,Universe),
		(N > Universe -> Sample is Universe; Sample is N)),
	get_clause_sample(Sample,Universe,CL,CList),
	keysort(CList,Clauses).

% sample_nclauses_using_modes(+N,+D,-Clauses)
% 	get upto N legal clauses using mode declarations
%	and distribution D over clauselengths

sample_nclauses_using_modes(0,_,[]):- !.
sample_nclauses_using_modes(N,D,[Clause|Rest]):-
	legal_clause_using_modes(100,D,Clause),
	N1 is N - 1,
	sample_nclauses_using_modes(N1,D,Rest).

% legal_clause_using_modes(+N,+D,-Clause)
%	make at most N attempts to obtain a legal clause Clause
%	from mode language using distribution D over clauselengths
%	if all N attempts fail, then just return most general clause
legal_clause_using_modes(N,D,L-[0,0,[],Clause]):-
	N > 0,
	sample_clause_using_modes(D,L,Clause),
	not(prune(Clause)),
	split_clause(Clause,Head,Body),
	(setting(language,Lang) ->
        	lang_ok(Head,Body,Lang);
		true),
	(setting(newvars,NewVars) ->
		newvars_ok(Head,Body,NewVars);
		true),
	!.
legal_clause_using_modes(N,D,Clause):-
	N > 1,
	N1 is N - 1,
	legal_clause_using_modes(N1,D,Clause), !.
legal_clause_using_modes(_,_,1-[0,0,[],Clause]):-
	sample_clause_using_modes([1.0-1],1,Clause).

sample_clause_using_modes(D,L,Clause):-
	findall(H,auto_refine(false,H),HL),
	HL \= [],
	random_select(Head,HL,_),
	draw_element(D,L),
	(L = 1 -> Clause = Head;
		L1 is L - 1,
		sample_clause_using_modes(L1,Head,Clause)).

sample_clause_using_modes(N,ClauseSoFar,Clause):-
	findall(C,auto_refine(ClauseSoFar,C),CL),
	CL \= [], !,
	(N = 1 -> random_select(Clause,CL,_);
		random_select(C1,CL,_),
		N1 is N - 1,
		sample_clause_using_modes(N1,C1,Clause)).
sample_clause_using_modes(_,Clause,Clause).


% get_clause_sample(+N,+U,+CL,-Clauses)
% 	get upto N legal clauses of at most length CL drawn from universe U
%	U is either the total number of legal clauses
%		or a distribution over clauselengths
%	the clauses are constructed by drawing randomly from bottom
get_clause_sample(0,_,_,[]):- !.
get_clause_sample(N,Universe,CL,[L-[E,T,C1,C]|Clauses]):-
        (number(Universe) ->
		get_rrandom(Universe,ClauseNum),
		num_to_length(ClauseNum,CL,L),
		UpperLim is CL;
		draw_element(Universe,L),
		UpperLim is L),
	draw_legalclause_wo_repl(L,UpperLim,C,C1), !,
	recorded(sat,sat(E,T),_),
	N1 is N - 1,
	get_clause_sample(N1,Universe,CL,Clauses).
get_clause_sample(N,Universe,CL,Clauses):-
	N1 is N - 1,
	get_clause_sample(N1,Universe,CL,Clauses).

% draw_legalclause_wo_repl(+L,+CL,-C,-Lits)
%	randomly draw without replacement a legal clause of length >= L and =< CL 
%	also returns literals from bottom used to construct clause
draw_legalclause_wo_repl(L,CL,C,C1):-
	L =< CL,
	randclause_wo_repl(L,C,legal,C1), !.
draw_legalclause_wo_repl(L,CL,C,C1):-
	L < CL,
	L1 is L + 1,
	draw_legalclause_wo_repl(L1, CL,C,C1).

% estimate_clauselength_distribution(+L,+T,+K,-D)
%	for each clauselength l <= L, estimate the probability of drawing a good clause
%	here, a ``good clause'' is one that is in the top K-percentile of clauses
%	estimation is by Monte Carlo using at most T trials
%	probabilities are normalised to add to 1
estimate_clauselength_distribution(L,T,K,D):-	
	recorded(sat,sat(Type,Example),_),
	recorded(random,clauselength_distribution(Type,Example,L,T,K,D),_), !.
estimate_clauselength_distribution(L,T,K,D):-	
	setting(evalfn,Evalfn),
	estimate_clauselength_scores(L,T,Evalfn,[],S),
	select_good_clauses(S,K,Good),
	estimate_frequency(L,Good,Freq),
	normalise_distribution(Freq,D),
	(recorded(sat,sat(Type,Example),_) ->
		recorda(random,clauselength_distribution(Type,Example,L,T,K,D),_);
		true).

estimate_clauselength_scores(0,_,_,S,S):- !.
estimate_clauselength_scores(L,T,Evalfn,S1,S):-
	set(clauselength_distribution,[1.0-L]),
	p1_message('Estimate scores of clauses with length'), p_message(L),
	sample_clauses(T,Clauses),
	estimate_scores(Clauses,Evalfn,S1,S2),
	L1 is L - 1,
	estimate_clauselength_scores(L1,T,Evalfn,S2,S).

estimate_scores([],_,S,S):- !.
estimate_scores([L-[_,_,_,C]|Rest],Evalfn,S1,S):-
	label_create(C,Label),
	extract_count(pos,Label,PC),
	extract_count(neg,Label,NC),
	complete_label(Evalfn,C,[PC,NC,L],[_,_,_,Val|_]),
	estimate_scores(Rest,Evalfn,[-Val-L|S1],S).
	
% ``good'' clauses are defined to be those in the top K-percentile
%	policy on ties is to include them
select_good_clauses(S,K,Good):-
	keysort(S,S1),
	length(S1,Total),
	N is integer(K*Total/100),
	select_good_clauses(S1,N,[],Good).

select_good_clauses([],_,Good,Good):- !.
select_good_clauses(_,N,Good,Good):- N =< 0, !.
select_good_clauses([Score-X|T],N,GoodSoFar,Good):-
	select_good_clauses(T,Score,N,[Score-X|GoodSoFar],N0,Good1,T1),
	N1 is N0 - 1,
	select_good_clauses(T1,N1,Good1,Good).

select_good_clauses([],_,N,G,N,G,[]):- !.
select_good_clauses([Score-X|T],Score,N,GoodSoFar,N0,Good1,T1):-
	!,
	N1 is N - 1,
	select_good_clauses(T,Score,N1,[Score-X|GoodSoFar],N0,Good1,T1).
select_good_clauses(L,_,N,G,N,G,L).

estimate_frequency(0,_,[]).
estimate_frequency(L,Good,[N-L|T]):-
	count_frequency(Good,L,N),
	L1 is L - 1,
	estimate_frequency(L1,Good,T).

count_frequency([],_,0).
count_frequency([Entry|T],X,N):-
	count_frequency(T,X,N1),
	(Entry = _-X -> N is N1 + 1; N is N1).

% estimate_numbers(+L,+Trials,+Sample,-T)
% 	estimate total number of legal clauses of length <= L in space bounded by bot
%	estimated number is cached for future use
%	estimation is by Monte Carlo, averaged over Trials trials with given sample size
estimate_numbers(L,Trials,Sample,Total):-
	recorded(sat,sat(Type,Example),_),
	recorded(random,sample(Type,Example,L,Trials,Sample),_),
	recorded(random,hypothesis_space(Total),_), !.
estimate_numbers(L,Trials,Sample,Total):-
	retract_all(random,sample(_,_,_,_,_)),
	retract_all(random,hypothesis_space(_)),
	estimate_numbers(L,Trials,Sample,0,Total),
	recorda(random,hypothesis_space(Total),_),
	recorded(sat,sat(Type,Example),_),
	recorda(random,sample(Type,Example,L,Trials,Sample),_).

% estimate_numbers(+L,+Trials,+Sample,+TotalSoFar,-Total)
%	estimate the number of legal clauses of length <= L
%	estimated number of legal clauses at each length are cached for future use
%	TotalSoFar is an accumulator of the number legal clauses so far
%	Total is the cumulative total of the number of legal clauses
estimate_numbers(0,_,_,T,T):- !.
estimate_numbers(L,Trials,Sample,TotalSoFar,T):-
	retract_all(random,number_of_clauses(L,_)),
	estimate_number(Trials,Sample,L,T0),
	recorda(random,number_of_clauses(L,T0),_),
	L1 is L - 1,
	T1 is T0 + TotalSoFar,
	estimate_numbers(L1,Trials,Sample,T1,T).

% estimate_number(+T,+S,+L,-N)
%	monte carlo estimate of number of legal clauses of length L
%	estimate formed from average over T trials with sample S
estimate_number(_,_,L,0):-
        recorded(sat,last_lit(Last),_),
        Last < L, !.   
estimate_number(T,S,L,N):-
	T > 0,
	p1_message('Estimate legal clauses with length'), p_message(L),
	estimate_number(T,S,0,L,Total),
	N is ceiling(Total/T),
	concat(['trials=',T,' sample=', S, ' estimate=', N],Mess),
	p_message(Mess).

estimate_number(1,S,Total,L,N):-
	!,
	estimate_number(L,S,N1),
	N is Total + N1.
estimate_number(T,S,Total,L,N):-
	p_message('New Trial'),
	estimate_number(L,S,N1),
	Total1 is Total + N1,
	T1 is T - 1,
	estimate_number(T1,S,Total1,L,N).

% estimate_number(+L,+S,-N)
%	estimate the number of legal clauses of length L in the search space
%	estimation based on sample size S
estimate_number(1,_,1):- !.
estimate_number(L,S,N):-
	estimate_proportion(S,L,legal,P,_),
	recorded(sat,last_lit(Last),_),
	total_clauses(L,Last,Total),
	N is ceiling(P*Total).

% estimate_proportion(+N,+L,+S,-P,-Clauses)
%	estimate prop. of at most N random clauses of length L and status S
%	clauses are generated without replacement
%	S is one of legal or illegal depending on whether C is inside or
%		outside the mode language provided
%	Clauses is the list of at most N def. clauses
%	If S is a variable then clauses can be legal or illegal
%	Thus estimate_proportion(10000,2,S,P,C) returns the
%		proportion and list of 2 literal clauses which are either
%		legal or illegal in a sample of at most 10000
%	Keeps legal clauses obtained in rselect_legal for later use
estimate_proportion(0,_,_,0,[]):- !.
estimate_proportion(N,L,S,P,Clauses):-
	retract_all(random,rselect(_)),
	retract_all(random,rselect_legal(_,_,_,_,_)),
	get_random_wo_repl(N,L,Clauses),
	length(Clauses,Total),
	count_clause_status(Clauses,S,A,_),
	(Total = 0 -> P = 0; P is A/Total),
	recorded(sat,sat(E,T),_),
	retract_all(random,rselect(_)),
	store_legal_clauses(Clauses,L,E,T).

% get_random_wo_repl(+N,+L,-List)
%	randomly construct at most N definite clauses of length L
%	returns Status/Clause list where Status is one of legal/illegal
get_random_wo_repl(0,_,[]):- !.
get_random_wo_repl(N,L,[S/[C,C1]|Clauses]):-
	randclause_wo_repl(L,C,S,C1), !,
	N1 is N - 1,
	get_random_wo_repl(N1,L,Clauses).
get_random_wo_repl(_,_,[]).

% print_distribution
print_distribution:-
	write('Clause Length'), tab(8), write('Estimated number of clauses'), nl,
	write('_____________'), tab(8), write('___________________________'), nl,
	findall(L-N,(recorded(random,number_of_clauses(L,N),_)),List),
	sort(List,List1),
	aleph_member(L-N,List1),
	write(L), tab(20), write(N), nl,
	fail.
print_distribution:-
	nl,
	write('Estimated size of hypothesis space = '),
	(recorded(random,hypothesis_space(S),_) -> true; S = 0),
	write(S), write(' clauses'), nl.
	
% count_clause_status(+List,+Status,-C1,-C2)
%	count number of clauses in List with status Status
%	C1 is the number of such clauses
%	C2 is the number of clauses with some other status
count_clause_status(_,S,_,0):-
	var(S), !.
count_clause_status(Clauses,S,A,B):-
	count_clause_status1(Clauses,S,A,B).

count_clause_status1([],_,0,0):- !.
count_clause_status1([S1/_|T],S,A,B):-
	count_clause_status1(T,S,A1,B1),
	(S == S1 -> A is A1 + 1, B is B1; A is A1, B is B1 + 1).

% store_legal_clauses(+List,+L,+E,+T)
% store all legal clauses of length L obtained with bottom clause for
% example E of type T
% useful later when a random legal clause of length L is required
store_legal_clauses([],_,_,_).
store_legal_clauses([S/[C,C1]|Clauses],L,E,T):-
	(S == legal -> recorda(random,rselect_legal(L,E,T,C,C1),_); true),
	store_legal_clauses(Clauses,L,E,T).

% randclause_wo_repl(+L,-C,-S,-Lits)
% as randclause/4 but ensures that clause obtained is without replacement
%	only makes at most 100 attempts to find such a clause
%	also returns lits from bottom clause selected
%	if all attempts fail, then return the most general clause
randclause_wo_repl(L,C,S,C1):-
	randclause_wo_repl(100,L,C,S,C1).

randclause_wo_repl(N,L,C,S,C1):-
	N > 0,
	randclause(L,C,S,C1),	% if not accounting for variable renamings
	% copy_term(C,C1),	% if accounting for variable renamings	
	% numbervars(C1,0,_),	% if accounting for variable renamings
	not(prune(C)),
	split_clause(C,Head,Body),
	(setting(language,Lang) ->
		lang_ok(Head,Body,Lang);
		true),
	(setting(newvars,NewVars) ->
		newvars_ok(Head,Body,NewVars);
		true),
	not(recorded(random,rselect(C1),_)), !,
	recorda(random,rselect(C1),_).
randclause_wo_repl(N,L,C,S,C1):-
	N > 0,
	N1 is N - 1,
	randclause_wo_repl(N1,L,C,S,C1), !.
randclause_wo_repl(_,1,C,S,C1):-
	randclause(1,C,S,C1).	% if not accounting for variable renamings
	% copy_term(C,C1),	% if accounting for variable renamings	
	% numbervars(C1,0,_),	% if accounting for variable renamings

% randclause(+L,-C,-S,-Lits)
%	returns definite clause C of length L with status S comprised of Lits
%	drawn at random from the bottom clause
%	also returns the literals in the bottom clause that were selected
%	body literals of C are randomly selected from the bottom clause
%	S is one of legal or illegal depending on whether C is inside or
%		outside the mode language provided
% needs a bottom clause to be constructed before it is meaningful
% this can be done with the sat predicate for eg: sat(1)
% if set(store_bottom,true) then use stored bottom clause instead
% if S is legal, then checks to see if previously generated legal
% clauses exist for this bottom clauses (these would have been generated
% when trying to estimate the number of legal clause at each length)
randclause(1,C,legal,[1]):-
	!,
	bottom_keys(_,_,Keys,_),
	arg(2,Keys,LitsKey),
	get_pclause([1],LitsKey,[],C,_,_,_).
randclause(L,C,Status,Lits):-
	Status == legal,
	recorded(sat,sat(E,T),_),
	recorded(random,rselect_legal(L,E,T,C,Lits),_).
% can do things more efficiently if we want to generate legal clauses only
randclause(L,C,Status,Lits):-
	Status == legal, !,
	bottom_keys(_,_,Keys,_),
	arg(2,Keys,LitsKey),
	arg(3,Keys,OVarsKey),
	arg(4,Keys,IVarsKey),
        recorded(LitsKey,lit_info(1,_,_,_,_,D),_),
        L1 is L - 1,
        repeat,
        randselect1(L1,LitsKey,D,[1],BodyLits),
        Lits = [1|BodyLits],
	clause_status(Lits,LitsKey,OVarsKey,IVarsKey,[],legal,legal), !,
        get_pclause(Lits,LitsKey,[],C,_,_,_).
randclause(L,C,Status,Lits):-
	L1 is L - 1,
	bottom_keys(_,_,Keys,_),
	arg(1,Keys,SatKey),
	arg(2,Keys,LitsKey),
	arg(3,Keys,OVarsKey),
	arg(4,Keys,IVarsKey),
	recorded(SatKey,last_lit(Last),_),
	repeat,
	randselect(L1,Last,LitsKey,[],BodyLits),
	aleph_append(BodyLits,[1],Lits),
	clause_status(Lits,LitsKey,OVarsKey,IVarsKey,[],legal,Status1),
	Status1 = Status, !,
	get_pclause(Lits,LitsKey,[],C,_,_,_).

% clause_status(+Lits,+LitsSoFar,+StatusSoFar,-Status)
% compute status of a clause
%	Lits is the lits left to add to the clause
%	LitsSoFar is the lits in the clause so far
%	StatusSoFar is the Status of the clause so far
%		if a literal to be added contains unbound input vars then
%		status is illegal
clause_status(Lits,LitsSoFar,Status1,Status2):-
	bottom_keys(_,_,Keys,_),
	arg(2,Keys,LitsKey),
	arg(3,Keys,OVarsKey),
	arg(4,Keys,IVarsKey),
	clause_status(Lits,LitsKey,OVarsKey,IVarsKey,LitsSoFar,Status1,Status2).

% as above, but with Keys specified
clause_status(Lits,Keys,LitsSoFar,Status1,Status2):-
	arg(2,Keys,LitsKey),
	arg(3,Keys,OVarsKey),
	arg(4,Keys,IVarsKey),
	clause_status(Lits,LitsKey,OVarsKey,IVarsKey,LitsSoFar,Status1,Status2).

clause_status([],_,_,_,_,S,S):- !.
clause_status([Lit|Lits],LitsKey,OVarsKey,IVarsKey,LitsSoFar,S,S1):-
	get_ovars(LitsSoFar,OVarsKey,LitsKey,[],OVars),
	get_ivars([Lit],IVarsKey,LitsKey,[],IVars),
	aleph_subset1(IVars,OVars), !,
	aleph_append([Lit],LitsSoFar,Lits1),
	clause_status(Lits,LitsKey,OVarsKey,IVarsKey,Lits1,S,S1).
clause_status(_,_,_,_,_,_,illegal).

	
% randselect(+L,+Last,+Key,+LitsSoFar,-Lits)
% randomly select L distinct literals to give Lits
% Last is the last literal number in the bottom clause
% LitsSoFar is the literals selected so far
randselect(0,_,_,_,[]):- !.
randselect(_,Last,_,LitsSoFar,[]):-
        length(LitsSoFar,L1),
        L1 is Last - 1, !.
randselect(L,Last,Key,LitsSoFar,[LitNum|Lits]):-
	get_rand_lit(Last,Key,LitsSoFar,LitNum),
	L1 is L - 1,
	randselect(L1,Last,Key,[LitNum|LitsSoFar],Lits).

% randselect1(+L,+Key,+Avail,+LitsSoFar,-Lits)
% randomly select L distinct literals from Avail to give Lits
% LitsSoFar is the literals selected so far
randselect1(0,_,_,_,[]):- !.
randselect1(_,_,[],_,[]):- !.
randselect1(L,Key,Avail,LitsSoFar,[LitNum|Lits]):-
	random_select(LitNum,Avail,Left),
        recorded(Key,lit_info(LitNum,_,_,_,_,D),_),
        update_list(D,Left,Left1),
        delete_list([LitNum|LitsSoFar],Left1,Avail1),
        L1 is L - 1,
        randselect1(L1,Key,Avail1,[LitNum|LitsSoFar],Lits).
 
% get_rand_lit(+Last,+Key,+LitsSoFar,-LitNum)
% randomly select a literal number from 2 - Last
% and not in list LitsSoFar
%	2 because 1 is reserved for head literal
get_rand_lit(Last,Key,LitsSoFar,LitNum):-
	repeat,
	get_rand_lit(Last,Key,LitNum),
	not(aleph_member(LitNum,LitsSoFar)),
	!.

% have to use repeat/0 in case literal number from random no generator
%	no longer exists in lits database
get_rand_lit(Last,Key,LitNum):-
	repeat,
	get_random(Last,LitNum),
	LitNum > 1,
	recorded(Key,lit_info(LitNum,_,_,_,_,_),_), !.

% total_clauses(+L,+N1,-N2)
%	total number of clauses of length L is N2
%	constructed from bottom clause of length N1
total_clauses(1,_,1.0):- !.
total_clauses(L,Bot,N):-
	L1 is L - 1,
	Bot1 is Bot - 1,
	total_clauses(L1,Bot1,N1),
	N is N1*Bot1.

% num_to_length(+N,+CL,-L)
%	find length of clause numbered N
%	clause length should be =< CL

num_to_length(N,_,1):- N =< 1.0, !.
num_to_length(N,CL,L):-
	num_to_length1(2,CL,N,1,L).

num_to_length1(L,CL,_,_,CL):-
	L >= CL, !.
num_to_length1(L,CL,N,TotalSoFar,Length):-
	recorded(random,number_of_clauses(L,T),_),
	NClauses is TotalSoFar + T,
	(N =< NClauses ->  
		(T < 1.0 -> Length is L - 1; Length = L) ;
		L1 is L + 1,
		num_to_length1(L1,CL,N,NClauses,Length)).

% refinement operator for randomised local search
%	Type is one of clauses or theories
%		if Type=clauses then assumes bottom clauses are present
%		if Type=theories then assumes bottom clauses are absent
rls_refine(clauses,_-[_,_,_,false],Clause):-
	!,
	sample_clauses(1,[Clause]),
	not(old_move(clauses,rls,Clause)).
rls_refine(clauses,Clause1,Clause2):-
	setting(moves,MaxMoves),
	once(recorded(rls,move(M),DbRef)),
	M =< MaxMoves,
	p1_message('move'), p_message(M),
	erase(DbRef),
	M1 is M + 1,
	recorda(rls,move(M1),_),
	clause_move(Move,Clause1,Clause2),
	(setting(rls_move_prob,Prob) ->
		X is random,
		X < Prob;
		true),
	p_message(Move),
	not(old_move(clauses,rls,Clause2)).

rls_refine(theories,[_-[_,_,_,false]],Theory):-
	!,
	once(theory_move(add_clause,[],Theory)),
	not(old_move(theories,rls,Theory)).
rls_refine(theories,Theory1,Theory2):-
	setting(moves,MaxMoves),
	once(recorded(rls,move(M),DbRef)),
	M =< MaxMoves,
	p1_message('move'), p_message(M),
	erase(DbRef),
	M1 is M + 1,
	recorda(rls,move(M1),_),
	theory_move(_,Theory1,Theory2),
	not(old_move(theories,rls,Theory2)).

% mcmc_refine(+Theory1,-Theory2)
% refinement operator for markov chain monte carlo search
%	operates at the theory level only
mcmc_refine([_-[_,_,_,false]],Theory):-
	!,
	once(theory_move(add_clause,[],Theory)).
mcmc_refine(Theory1,Theory2):-
	recorded(mcmc,parent_stats(_,PCvr,NCvr),_),
	mcmc_select_example(PCvr,NCvr,Example,Type),
	mcmc_refine(Type,Example,Theory1,Theory2).

mcmc_select_example(Pos,Neg,E,T):-
	recorded(aleph,atoms(pos,AllPos),_),
	rm_intervals(Pos,AllPos,PLeft),
	interval_count(PLeft,P),
	interval_count(Neg,N),
	PFrac is P/(N+0.001),
	X is random,
	(X =< PFrac ->
		T = pos,
		get_random(P,R),
		interval_select(R,PLeft,E);
		T = neg,
		get_random(N,R),
		interval_select(R,Neg,E)), !.

mcmc_refine(pos,N,T1,T2):-
	length(T1,L),
	setting(clauses,Max),
	X is random,
	((L < Max, X =< 0.5) ->
		sat(pos,N),
		theory_move(add_clause,T1,T2);
		example(N,pos,E),
		theory_move(delete_lit,T1,T2),
		retract_all(pclause),
		record_pclauses(T2,_),
		once(E)).
mcmc_refine(neg,N,T1,T2):-
	example(N,neg,E),
	length(T1,L),
	X is random,
	((L > 1, X =< 0.5) ->
		theory_move(delete_clause,T1,T2);
		theory_move(add_lit,T1,T2)),
	retract_all(pclause),
	record_pclauses(T2,_),
	not(E).


% clause_move(+Type,+C1,-C2)
% local moves from clause C1 to give C2
%	A move is:
%	a) delete a literal from C1 (Type = delete_lit)
%	b) add a legal literal to C1 (Type = add_lit)
clause_move(delete_lit,C1,C2):-
	C1 = L-[E,T,Lits,Clause],
	(Lits = [H|Rest] ->
		aleph_delete(_,Rest,Left),
		Lits1 = [H|Left],
		bottom_keys(E,T,Keys,_),
		clause_status(Lits1,Keys,[],legal,legal),
		arg(2,Keys,LitsKey),
		L1 is L - 1,
        	get_pclause(Lits1,LitsKey,[],Clause1,_,_,_),
		not(prune(Clause1)) ;
		clause_to_list(Clause,[Head|Body]),
		aleph_delete(_,Body,Left),
		aleph_mode_linked([Head|Left]),
		list_to_clause([Head|Left],Clause1),
		not(prune(Clause1)),
		L1 is L - 1,
		Lits1 = []),
	C2 = L1-[E,T,Lits1,Clause1].
clause_move(add_lit,C1,C2):-
	C1 = L-[E,T,Lits,Clause],
	setting(clauselength,CL),
	L < CL,
	(Lits = [] ->
		auto_refine(Clause,Clause1),
		L1 is L + 1,
		Lits1 = [];
		aleph_delete(Lit,Lits,Left),
		bottom_keys(E,T,Keys,_),
		arg(2,Keys,LitsKey),
        	recorded(LitsKey,lit_info(Lit,_,_,_,_,D),_),
		aleph_member(Lit1,D),
		not(aleph_member(Lit1,Left)),
		aleph_append([Lit1],Lits,Lits1),
        	clause_status(Lits1,Keys,[],legal,legal),
		L1 is L + 1,
        	get_pclause(Lits1,LitsKey,[],Clause1,_,_,_),
		not(prune(Clause1))),
	C2 = L1-[E,T,Lits1,Clause1].

% theory_move(+Type,+T1,-T2)
% local moves from theory T1 to give T2
%	A move is:
%	a) delete a clause from T1 (Type = delete_clause)
%	b) add a legal clause to  T1  (Type = add_clause)
%	c) delete a literal from a clause in T1 (Type = delete_lit)
%	d) add a legal literal to a clause in T1 (Type = add_lit)
theory_move(delete_clause,T1,T2):-
	aleph_delete(_,T1,T2),
	T2 \= [].
theory_move(add_clause,T1,T2):-
	setting(clauses,Max),
	length(T1,L),
	L < Max,
	sample_clauses(1,[Clause]),
	aleph_append([Clause],T1,T2).
theory_move(delete_lit,T1,T2):-
	aleph_delete(Clause,T1,T),
	clause_move(delete_lit,Clause,Clause1),
	aleph_append([Clause1],T,T2).
theory_move(add_lit,T1,T2):-
	aleph_delete(Clause,T1,T),
	clause_move(add_lit,Clause,Clause1),
	aleph_append([Clause1],T,T2).

old_move(clauses,Key,N-[_,_,L,C]):-
	(setting(cache_clauselength,N1) -> true; N1 = 3),
	N =< N1,
	(L = [] ->
		clause_to_list(C,C1),
		sort(C1,Hash),
		numbervars(Hash,0,_);
		sort(L,Hash)),
	(recorded(Key,seen(N,Hash),_) ->
		p_message('old move'),
		true;
		recorda(Key,seen(N,Hash),_), !,
		fail).
old_move(theories,Key,T):-
	% remove_alpha_variants(T,T1),
	numbervars(T,0,_),
	length(T,N),
	(recorded(Key,seen(N,T),_) -> 
		p_message('old move'),
		true;
		recorda(Key,seen(N,T),_), !,
		fail).
		
extract_clauses_with_length([],[]).
extract_clauses_with_length([L-[_,_,_,C]|T],[L-C|T1]):-
	extract_clauses_with_length(T,T1).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% U T I L I T I E S

% concatenate elements of a list into an atom

concat([Atom],Atom):- !.
concat([H|T],Atom):-
        concat(T,AT),
        name(AT,L2),
        name(H,L1),
        aleph_append(L2,L1,L),
        name(Atom,L).


split_clause((Head:-true),Head,true):- !.
split_clause((Head:-Body1),Head,Body2):- !, Body1 = Body2.
split_clause([Head|T],Head,T):- !.
split_clause([Head],Head,[true]):- !.
split_clause(Head,Head,true).

strip_true((Head:-true),Head):- !.
strip_true(Clause,Clause).

% pretty print a definite clause
pp_dclause(Clause):-
        (recorded(aleph,set(portray_literals,true),_)->
                pp_dclause(Clause,true);
                pp_dclause(Clause,false)).

% pretty print a set of definite clauses
pp_dclauses(Theory):-
        aleph_member(_-[_,_,_,Clause],Theory),
        pp_dclause(Clause),
        fail.
pp_dclauses(_):- nl.
 
pp_dclause((H:-true),Pretty):-
        !,
        pp_dclause(H,Pretty).
pp_dclause((H:-B),Pretty):-
        !,
        copy_term((H:-B),(Head:-Body)),
% ICD:  numbervars((Head:-Body),0,_),
        numbervars_nosingletons((Head:-Body),0,_),
        aleph_portray(Pretty,Head),
        (Pretty = true ->
                write(' if:');
                write(' :-')),
        nl,
        recorded(aleph,set(print,N),_),
        print_lits(Body,Pretty,1,N).

pp_dclause((Lit),Pretty):-
        copy_term(Lit,Lit1),
% ICD:  numbervars(Lit1,0,_),
        numbervars_nosingletons(Lit1,0,_),
        aleph_portray(Pretty,Lit1),
        write('.'), nl.
 
% pretty print a definite clause list: head of list is + literal
pp_dlist([]):- !.
pp_dlist(Clause):-
        (recorded(aleph,set(portray_literals,true),_)->
                pp_dlist(Clause,true);
                pp_dlist(Clause,false)).
 
pp_dlist(Clause,Pretty):-
        copy_term(Clause,[Head1|Body1]),
% ICD:  numbervars([Head1|Body1],0,_),
        numbervars_nosingletons([Head1|Body1],0,_),
        aleph_portray(Pretty,Head1),
        (Body1 = [] ->
                print('.'), nl;
                (Pretty = true ->
                        write(' if:');
                        write(' :-')),
        nl,
        recorded(aleph,set(print,N),_),
        print_litlist(Body1,Pretty,1,N)).
 
print_litlist([],_,_,_).
print_litlist([Lit],Pretty,LitNum,_):-
        !,
        print_lit(Lit,Pretty,LitNum,LitNum,'.',_).
print_litlist([Lit|Lits],Pretty,LitNum,LastLit):-
        print_lit(Lit,Pretty,LitNum,LastLit,', ',NextLit),
        print_litlist(Lits,Pretty,NextLit,LastLit).
 
print_lits((Lit,Lits),Pretty,LitNum,LastLit):-
        !,
        (Pretty = true ->
                Sep = ' and ';
                Sep = ', '),
        print_lit(Lit,Pretty,LitNum,LastLit,Sep,NextLit),
        print_lits(Lits,Pretty,NextLit,LastLit).
print_lits((Lit),Pretty,LitNum,_):-
        print_lit(Lit,Pretty,LitNum,LitNum,'.',_).

print_lit(Lit,Pretty,LitNum,LastLit,Sep,NextLit):-
        (LitNum = 1 -> tab(3);true),
        aleph_portray(Pretty,Lit), write(Sep),
        (LitNum=LastLit-> nl,NextLit=1; NextLit is LitNum + 1).
 

p1_message(Mess):-
	print('['), print(Mess), print('] ').

p_message(Mess):-
	print('['), print(Mess), print(']'), nl.

aleph_delete_all(_,[],[]).
aleph_delete_all(X,[Y|T],T1):-
        X == Y, !,
        aleph_delete_all(X,T,T1).
aleph_delete_all(X,[Y|T],[Y|T1]):-
        aleph_delete_all(X,T,T1).

delete_list([],L,L).
delete_list([H1|T1],L1,L):-
	aleph_delete(H1,L1,L2), !,
	delete_list(T1,L2,L).
delete_list([_|T1],L1,L):-
	delete_list(T1,L1,L).

aleph_delete(H,[H|T],T).
aleph_delete(H,[H1|T],[H1|T1]):-
	aleph_delete(H,T,T1).

aleph_delete1(H,[H|T],T):- !.
aleph_delete1(H,[H1|T],[H1|T1]):-
	aleph_delete1(H,T,T1).

aleph_delete0(_,[],[]).
aleph_delete0(H,[H|T],T):- !.
aleph_delete0(H,[H1|T],[H1|T1]):-
	aleph_delete0(H,T,T1).

aleph_append(A,[],A).
aleph_append(A,[H|T],[H|T1]):-
	aleph_append(A,T,T1).

% remove_nth(+N,+List1,-Elem,-List2)
%	remove the nth elem from a List
remove_nth(1,[H|T],H,T):- !.
remove_nth(N,[H|T],X,[H|T1]):-
        N1 is N - 1,
        remove_nth(N1,T,X,T1).
	
% get_first_n(+N,+List1,-List2)
%	get the first n elements in List1
get_first_n(0,_,[]):- !.
get_first_n(_,[],[]):- !.
get_first_n(N,[H|T],[H|T1]):-
	N1 is N - 1,
	get_first_n(N1,T,T1).

% max_in_list(+List,-Max)
%	return largest element in a list
max_in_list([X],X):- !.
max_in_list([X|T],Z):-
	max_in_list(T,Y),
	(X @> Y -> Z = X; Z = Y). 

% min_in_list(+List,-Max)
%	return largest element in a list
min_in_list([X],X):- !.
min_in_list([X|T],Z):-
	min_in_list(T,Y),
	(X @> Y -> Z = Y; Z = X). 

% remove_alpha_variants(+List1,-List2):-
%	remove alphabetic variants from List1 to give List2
remove_alpha_variants([],[]).
remove_alpha_variants([X|Y],L):-
	aleph_member(X1,Y),
	alphabetic_variant(X,X1), !,
	remove_alpha_variants(Y,L).
remove_alpha_variants([X|Y],[X|L]):-
	remove_alpha_variants(Y,L).
 
% alphabetic_variant(+Term1,+Term2)
%	true if Term1 is the alphabetic variant of Term2
alphabetic_variant(Term1,Term2):-
	copy_term(Term1/Term2,T1/T2),
	numbervars(T1,0,_),
	numbervars(T2,0,_),
	T1 = T2.

% tparg(+TermPlace,+Term1,?Term2)
% return Term2 at position specified by TermPlace in Term1
tparg([Place],Term,Arg):-
        !,
        arg(Place,Term,Arg).
tparg([Place|Places],Term,Arg):-
        arg(Place,Term,Term1),
        tparg(Places,Term1,Arg).


aleph_member1(H,[H|_]):- !.
aleph_member1(H,[_|T]):-
	aleph_member1(H,T).

aleph_member2(X,[Y|_]):- X == Y, !.
aleph_member2(X,[_|T]):-
	aleph_member2(X,T).

aleph_member(X,[X|_]).
aleph_member(X,[_|T]):-
	aleph_member(X,T).

aleph_reverse(L1, L2) :- revzap(L1, [], L2).

revzap([X|L], L2, L3) :- revzap(L, [X|L2], L3).
revzap([], L, L).

 
goals_to_clause((Head,Body),(Head:-Body)):- !.
goals_to_clause(Head,Head).

clause_to_list((Head:-true),[Head]):- !.
clause_to_list((Head:-Body),[Head|L]):-
        !,
        goals_to_list(Body,L).
clause_to_list(Head,[Head]).

extend_clause(false,Lit,(Lit)):- !.
extend_clause((Head:-Body),Lit,(Head:-Body1)):-
        !,
        app_lit(Lit,Body,Body1).
extend_clause(Head,Lit,(Head:-Lit)).
 
app_lit(L,(L1,L2),(L1,L3)):-
        !,
        app_lit(L,L2,L3).
app_lit(L,L1,(L1,L)).

prefix_lits(L,true,L):- !.
prefix_lits(L,L1,((L),L1)).

nlits((_:-B),N):-
	!,
	nlits(B,N1),
	N is N1 + 1.
nlits((_,Lits),N):-
	!,
	nlits(Lits,N1),
	N is N1 + 1.
nlits(_,1).


list_to_clause([Goal],(Goal:-true)):- !.
list_to_clause([Head|Goals],(Head:-Body)):-
	list_to_goals(Goals,Body).

list_to_goals([Goal],Goal):- !.
list_to_goals([Goal|Goals],(Goal,Goals1)):-
	list_to_goals(Goals,Goals1).

goals_to_list((true,Goals),T):-
	!,
	goals_to_list(Goals,T).
goals_to_list((Goal,Goals),[Goal|T]):-
	!,
	goals_to_list(Goals,T).
goals_to_list(true,[]):- !.
goals_to_list(Goal,[Goal]).

get_clause(LitNum,Last,_,[]):-
        LitNum > Last, !.
get_clause(LitNum,Last,TVSoFar,[FAtom|FAtoms]):-
        recorded(lits,lit_info(LitNum,_,Atom,_,_,_),_), !,
        get_flatatom(Atom,TVSoFar,FAtom,TV1),
        NextLit is LitNum + 1,
        get_clause(NextLit,Last,TV1,FAtoms).
get_clause(LitNum,Last,TVSoFar,FAtoms):-
        NextLit is LitNum + 1,
        get_clause(NextLit,Last,TVSoFar,FAtoms).

get_flatatom(not(Atom),TVSoFar,not(FAtom),TV1):-
        !,
        get_flatatom(Atom,TVSoFar,FAtom,TV1).
get_flatatom(Atom,TVSoFar,FAtom,TV1):-
        functor(Atom,Name,Arity),
        functor(FAtom,Name,Arity),
        flatten_args(Arity,Atom,FAtom,TVSoFar,TV1).

get_pclause([LitNum],TVSoFar,Clause,TV,Length,LastDepth):-
        !,
        get_pclause1([LitNum],TVSoFar,TV,Clause,Length,LastDepth).
get_pclause([LitNum|LitNums],TVSoFar,Clause,TV,Length,LastDepth):-
        get_pclause1([LitNum],TVSoFar,TV1,Head,Length1,_),
        get_pclause1(LitNums,TV1,TV,Body,Length2,LastDepth),
	Clause = (Head:-Body),
        Length is Length1 + Length2.

get_pclause1([LitNum],TVSoFar,TV1,Lit,Length,LastDepth):-
        !,
        recorded(lits,lit_info(LitNum,LastDepth,Atom,_,_,_),_),
        get_flatatom(Atom,TVSoFar,Lit,TV1),
        functor(Lit,Name,_),
        (Name = '='-> Length = 0; Length = 1).
get_pclause1([LitNum|LitNums],TVSoFar,TV2,(Lit,Lits1),Length,LastDepth):-
        recorded(lits,lit_info(LitNum,_,Atom,_,_,_),_),
        get_flatatom(Atom,TVSoFar,Lit,TV1),
        get_pclause1(LitNums,TV1,TV2,Lits1,Length1,LastDepth),
        functor(Lit,Name,_),
        (Name = '='-> Length = Length1; Length is Length1 + 1).

get_pclause([LitNum],Key,TVSoFar,Clause,TV,Length,LastDepth):-
        !,
        get_pclause1([LitNum],Key,TVSoFar,TV,Clause,Length,LastDepth).
get_pclause([LitNum|LitNums],Key,TVSoFar,Clause,TV,Length,LastDepth):-
        get_pclause1([LitNum],Key,TVSoFar,TV1,Head,Length1,_),
        get_pclause1(LitNums,Key,TV1,TV,Body,Length2,LastDepth),
	Clause = (Head:-Body),
        Length is Length1 + Length2.

get_pclause1([LitNum],Key,TVSoFar,TV1,Lit,Length,LastDepth):-
        !,
        recorded(Key,lit_info(LitNum,LastDepth,Atom,_,_,_),_),
        get_flatatom(Atom,TVSoFar,Lit,TV1),
        functor(Lit,Name,_),
        (Name = '='-> Length = 0; Length = 1).
get_pclause1([LitNum|LitNums],Key,TVSoFar,TV2,(Lit,Lits1),Length,LastDepth):-
        recorded(Key,lit_info(LitNum,_,Atom,_,_,_),_),
        get_flatatom(Atom,TVSoFar,Lit,TV1),
        get_pclause1(LitNums,Key,TV1,TV2,Lits1,Length1,LastDepth),
        functor(Lit,Name,_),
        (Name = '='-> Length = Length1; Length is Length1 + 1).


flatten_args(0,_,_,TV,TV):- !.
flatten_args(Arg,Atom,FAtom,TV,TV1):-
        arg(Arg,Atom,Term),
        Arg1 is Arg - 1,
        (Term = aleph_const(Const) ->
                arg(Arg,FAtom,Const),
                flatten_args(Arg1,Atom,FAtom,TV,TV1);
                (integer(Term) ->
                        update(TV,Term/Var,TV0),
                        arg(Arg,FAtom,Var),
                        flatten_args(Arg1,Atom,FAtom,TV0,TV1);
                        (functor(Term,Name,Arity),
                         functor(FTerm,Name,Arity),
                         arg(Arg,FAtom,FTerm),
                         flatten_args(Arity,Term,FTerm,TV,TV0),
                         flatten_args(Arg1,Atom,FAtom,TV0,TV1)
                        )
                )
        ).


% returns intersection of S1, S2 and S1-Intersection
intersect1(Elems,[],[],Elems):- !.
intersect1([],_,[],[]):- !.
intersect1([Elem|Elems],S2,[Elem|Intersect],ElemsLeft):-
	aleph_member1(Elem,S2), !,
	intersect1(Elems,S2,Intersect,ElemsLeft).
intersect1([Elem|Elems],S2,Intersect,[Elem|ElemsLeft]):-
	intersect1(Elems,S2,Intersect,ElemsLeft).

aleph_subset1([],_).
aleph_subset1([Elem|Elems],S):-
	aleph_member1(Elem,S), !,
	aleph_subset1(Elems,S).

% two sets are equal

equal_set([],[]).
equal_set([H|T],S):-
	aleph_delete1(H,S,S1),
	equal_set(T,S1), !.

uniq_insert(_,X,[],[X]).
uniq_insert(descending,H,[H1|T],[H,H1|T]):-
	H @> H1, !.
uniq_insert(ascending,H,[H1|T],[H,H1|T]):-
	H @< H1, !.
uniq_insert(_,H,[H|T],[H|T]):- !.
uniq_insert(Order,H,[H1|T],[H1|T1]):-
	!,
	uniq_insert(Order,H,T,T1).


quicksort(_,[],[]).
quicksort(Order,[X|Tail],Sorted):-
	partition(X,Tail,Small,Big),
	quicksort(Order,Small,SSmall),
	quicksort(Order,Big,SBig),
        (Order=ascending-> aleph_append([X|SBig],SSmall,Sorted);
                aleph_append([X|SSmall],SBig,Sorted)).
	

partition(_,[],[],[]).
partition(X,[Y|Tail],[Y|Small],Big):-
	X @> Y, !,
	partition(X,Tail,Small,Big).
partition(X,[Y|Tail],Small,[Y|Big]):-
	partition(X,Tail,Small,Big).

update_list([],L,L).
update_list([H|T],L,Updated):-
	update(L,H,L1), !,
	update_list(T,L1,Updated).

update([],H,[H]).
update([H|T],H,[H|T]):- !.
update([H1|T],H,[H1|T1]):-
	update(T,H,T1).

% checks if 2 sets intersect
intersects(S1,S2):-
	aleph_member(Elem,S1), aleph_member1(Elem,S2), !.

% checks if bitsets represented as lists of intervals intersect
intervals_intersects([L1-L2|_],I):-
	intervals_intersects1(L1-L2,I), !.
intervals_intersects([_|I1],I):-
	intervals_intersects(I1,I).

intervals_intersects1(L1-_,[M1-M2|_]):-
	L1 >= M1, L1 =< M2, !.
intervals_intersects1(L1-L2,[M1-_|_]):-
	M1 >= L1, M1 =< L2, !.
intervals_intersects1(L1-L2,[_|T]):-
	intervals_intersects1(L1-L2,T).

% checks if bitsets represented as lists of intervals intersect
% returns first intersection
intervals_intersects([L1-L2|_],I,I1):-
	intervals_intersects1(L1-L2,I,I1), !.
intervals_intersects([_|ILeft],I,I1):-
	intervals_intersects(ILeft,I,I1).

intervals_intersects1(I1,[I2|_],I):-
	interval_intersection(I1,I2,I), !.
intervals_intersects1(I1,[_|T],I):-
	% intervals_intersection(I1,T,I).
	intervals_intersects1(I1,T,I).

interval_intersection(L1-L2,M1-M2,L1-L2):-
	L1 >= M1, L2 =< M2, !.
interval_intersection(L1-L2,M1-M2,M1-M2):-
	M1 >= L1, M2 =< L2, !.
interval_intersection(L1-L2,M1-M2,L1-M2):-
	L1 >= M1, M2 >= L1, M2 =< L2, !.
interval_intersection(L1-L2,M1-M2,M1-L2):-
	M1 >= L1, M1 =< L2, L2 =< M2, !.

%most of the time no intersection, so optimise on that
% optimisation by James Cussens
intervals_intersection([],_,[]).
intervals_intersection([A-B|T1],[C-D|T2],X) :-
        !,
        (A > D ->
            intervals_intersection([A-B|T1],T2,X);
            (C > B ->
                intervals_intersection(T1,[C-D|T2],X);
                (B > D ->
                    (C > A ->
                        X=[C-D|Y];
                        X=[A-D|Y]
                    ),
                    intervals_intersection([A-B|T1],T2,Y);
                    (C > A ->
                        X=[C-B|Y];
                        X=[A-B|Y]
                    ),
                    intervals_intersection(T1,[C-D|T2],Y)
                )
            )
        ).
intervals_intersection(_,[],[]).


% finds length of intervals in a list
interval_count([],0).
interval_count([L1-L2|T],N):-
	N1 is L2 - L1 + 1,
	interval_count(T,N2),
	N is N1 + N2.
interval_count(I/_,N):-
	interval_count(I,N).

% interval_select(+N,+List1,-Elem)
%       select the Nth elem from an interval list
interval_select(N,[A-B|_],X):-
        N =< B - A + 1, !,
        X is A + N - 1.
interval_select(N,[A-B|T],X):-
        N1 is N - (B - A + 1),
        interval_select(N1,T,X).


% convert list to intervals
list_to_intervals(List,Intervals):-
	sort(List,List1),
        list_to_intervals1(List1,Intervals).

list_to_intervals1([],[]).
list_to_intervals1([Start|T],[Start-Finish|I1]):-
        list_to_interval(Start,T,Finish,T1),
        list_to_intervals1(T1,I1).

list_to_interval(Finish,[],Finish,[]).
list_to_interval(Finish,[Next|T],Finish,[Next|T]):-
        Next - Finish > 1,
        !.
list_to_interval(_,[Start|T],Finish,Rest):-
        list_to_interval(Start,T,Finish,Rest).

% converts intervals into a list
intervals_to_list([],[]).
intervals_to_list([Interval|Intervals],L):-
        interval_to_list(Interval,L1),
        intervals_to_list(Intervals,L2),
        aleph_append(L2,L1,L), !.

% converts an interval into a list
interval_to_list(Start-Finish,[]):-
	Start > Finish, !.
interval_to_list(Start-Finish,[Start|T]):-
	Start1 is Start+1,
	interval_to_list(Start1-Finish,T).

interval_subsumes(Start1-Finish1,Start2-Finish2):-
	Start1 =< Start2,
	Finish1 >= Finish2.

interval_subtract(Start1-Finish1,Start1-Finish1,[]):- !.
interval_subtract(Start1-Finish1,Start1-Finish2,[S2-Finish1]):-
	!,
	S2 is Finish2 + 1.
interval_subtract(Start1-Finish1,Start2-Finish1,[Start1-S1]):-
	!,
	S1 is Start2 - 1.
interval_subtract(Start1-Finish1,Start2-Finish2,[Start1-S1,S2-Finish1]):-
	S1 is Start2 - 1,
	S2 is Finish2 + 1,
	S1 >= Start1, Finish1 >= S2, !.


% code for set manipulation utilities 
% taken from the Yap library
% aleph_ord_subtract(+Set1,+Set2,?Difference)
% is true when Difference contains all and only the elements of Set1
% which are not also in Set2.
aleph_ord_subtract(Set1,[],Set1) :- !.
aleph_ord_subtract([],_,[]) :- !.
aleph_ord_subtract([Head1|Tail1],[Head2|Tail2],Difference) :-
        compare(Order,Head1,Head2),
        aleph_ord_subtract(Order,Head1,Tail1,Head2,Tail2,Difference).

aleph_ord_subtract(=,_,    Tail1,_,    Tail2,Difference) :-
	aleph_ord_subtract(Tail1,Tail2,Difference).
aleph_ord_subtract(<,Head1,Tail1,Head2,Tail2,[Head1|Difference]) :-
        aleph_ord_subtract(Tail1,[Head2|Tail2],Difference).
aleph_ord_subtract(>,Head1,Tail1,_,    Tail2,Difference) :-
        aleph_ord_subtract([Head1|Tail1],Tail2,Difference). 

% aleph_ord_disjoint(+Set1,+Set2)
% is true when the two ordered sets have no element in common.  If the
% arguments are not ordered,I have no idea what happens.
aleph_ord_disjoint([],_) :- !.
aleph_ord_disjoint(_,[]) :- !.
aleph_ord_disjoint([Head1|Tail1],[Head2|Tail2]) :-
        compare(Order,Head1,Head2),
        aleph_ord_disjoint(Order,Head1,Tail1,Head2,Tail2).

aleph_ord_disjoint(<,_,Tail1,Head2,Tail2) :-
        aleph_ord_disjoint(Tail1,[Head2|Tail2]).
aleph_ord_disjoint(>,Head1,Tail1,_,Tail2) :-
        aleph_ord_disjoint([Head1|Tail1],Tail2).


% aleph_ord_union(+Set1,+Set2,?Union)
% is true when Union is the union of Set1 and Set2.  Note that when
% something occurs in both sets,we want to retain only one copy.
aleph_ord_union(Set1,[],Set1) :- !.
aleph_ord_union([],Set2,Set2) :- !.
aleph_ord_union([Head1|Tail1],[Head2|Tail2],Union) :-
        compare(Order,Head1,Head2),
        aleph_ord_union(Order,Head1,Tail1,Head2,Tail2,Union).

aleph_ord_union(=,Head, Tail1,_,    Tail2,[Head|Union]) :-
        aleph_ord_union(Tail1,Tail2,Union).
aleph_ord_union(<,Head1,Tail1,Head2,Tail2,[Head1|Union]) :-
        aleph_ord_union(Tail1,[Head2|Tail2],Union).
aleph_ord_union(>,Head1,Tail1,Head2,Tail2,[Head2|Union]) :-
        aleph_ord_union([Head1|Tail1],Tail2,Union).

% aleph_ord_union(+Set1,+Set2,?Union,?Difference)
% is true when Union is the union of Set1 and Set2 and Difference is the
% difference between Set2 and Set1.
aleph_ord_union(Set1,[],Set1,[]) :- !.
aleph_ord_union([],Set2,Set2,Set2) :- !.
aleph_ord_union([Head1|Tail1],[Head2|Tail2],Union,Diff) :-
        compare(Order,Head1,Head2),
        aleph_ord_union(Order,Head1,Tail1,Head2,Tail2,Union,Diff).

aleph_ord_union(=,Head, Tail1,_, Tail2,[Head|Union],Diff) :-
        aleph_ord_union(Tail1,Tail2,Union,Diff).
aleph_ord_union(<,Head1,Tail1,Head2,Tail2,[Head1|Union],Diff) :-
        aleph_ord_union(Tail1,[Head2|Tail2],Union,Diff).
aleph_ord_union(>,Head1,Tail1,Head2,Tail2,[Head2|Union],[Head2|Diff]) :-
        aleph_ord_union([Head1|Tail1],Tail2,Union,Diff).

aleph_ord_intersection(_,[],[]) :- !.
aleph_ord_intersection([],_,[]) :- !.
aleph_ord_intersection([Head1|Tail1],[Head2|Tail2],Intersection) :-
        compare(Order,Head1,Head2),
        aleph_ord_intersection(Order,Head1,Tail1,Head2,Tail2,Intersection).

aleph_ord_intersection(=,Head,Tail1,_,Tail2,[Head|Intersection]) :-
        aleph_ord_intersection(Tail1,Tail2,Intersection).
aleph_ord_intersection(<,_,Tail1,Head2,Tail2,Intersection) :-
        aleph_ord_intersection(Tail1,[Head2|Tail2],Intersection).
aleph_ord_intersection(>,Head1,Tail1,_,Tail2,Intersection) :-
        aleph_ord_intersection([Head1|Tail1],Tail2,Intersection).


aleph_ord_subset([], _) :- !.
aleph_ord_subset([Head1|Tail1], [Head2|Tail2]) :-
        compare(Order, Head1, Head2),
        aleph_ord_subset(Order, Head1, Tail1, Head2, Tail2).

aleph_ord_subset(=, _, Tail1, _, Tail2) :-
        aleph_ord_subset(Tail1, Tail2).
aleph_ord_subset(>, Head1, Tail1, _, Tail2) :-
        aleph_ord_subset([Head1|Tail1], Tail2).

vars_in_term([],Vars,Vars1):- sort(Vars,Vars1), !.
vars_in_term([Var|T],VarsSoFar,Vars):-
        var(Var), !,
        vars_in_term(T,[Var|VarsSoFar],Vars).
vars_in_term([Term|T],VarsSoFar,Vars):-
        Term =.. [_|Terms], !,
        vars_in_term(Terms,VarsSoFar,V1),
        vars_in_term(T,V1,Vars).
vars_in_term([_|T],VarsSoFar,Vars):-
        vars_in_term(T,VarsSoFar,Vars).


occurs_in(Vars,(Lit,_)):-
	occurs_in(Vars,Lit), !.
occurs_in(Vars,(_,Lits)):-
	!,
	occurs_in(Vars,Lits).
occurs_in(Vars,Lit):-
	functor(Lit,_,Arity),
	occurs1(Vars,Lit,1,Arity).

occurs1(Vars,Lit,Argno,MaxArgs):- 
	Argno =< MaxArgs,
	arg(Argno,Lit,Term),
	vars_in_term([Term],[],Vars1),
	aleph_member(X,Vars), aleph_member(Y,Vars1), 
	X == Y, !.
occurs1(Vars,Lit,Argno,MaxArgs):- 
	Argno < MaxArgs,
	Next is Argno + 1,
	occurs1(Vars,Lit,Next,MaxArgs).

% compiler instructions
declare_dynamic(Pred/Arity):-
	dynamic Pred/Arity.

clean_up:-
        clean_up_init,
        clean_up_sat,
        clean_up_reduce.

clean_up_init:-
        retract_all(good),
	retract_all(bottom).

clean_up_sat:-
	retract_all(vars),
	retract_all(terms),
	retract_all(lits),
	retract_all(ivars),
	retract_all(ovars),
	retract_all(split),
	retract_all(sat),
	retract_all(atoms),
	retract_all(random),
	retract_all(aleph_dyn),
	retract_all(pclause),
	gc.

clean_up_reduce:-
	retract_all(search),
	retract_all(pclause),
	retract_all(openlist),
	retract_all(nodes),
	clean_up_node_indices,
	retract_all(gains),
	retract_all(aleph_dyn),
	gc.


retract_all(Key,Fact):-
	recorded(Key,Fact,DbRef),
	erase(DbRef),
	fail.
retract_all(_,_).

retract_all(Key):-
	eraseall(Key), !.
retract_all(_).

clean_up_node_indices:-
	setting(nodes,MaxNodes), !,
	LastIndex is MaxNodes // 1000,
	clean_up_node_indices(LastIndex).
clean_up_node_indices.
	
clean_up_node_indices(Index):- Index < 0, !.
clean_up_node_indices(Index):- 
	retract_all(Index), !,
        NextIndex is Index - 1,
        clean_up_node_indices(NextIndex).
clean_up_node_indices(Index):-
        NextIndex is Index - 1,
        clean_up_node_indices(NextIndex).

depth_bound_call(G):-
	recorded(aleph,set(depth,D),_),
	depth_bound_call(G,D).

binom_lte(_,_,O,0.0):- O < 0, !.
binom_lte(N,P,O,Prob):-
        binom(N,P,O,Prob1),
        O1 is O - 1,
        binom_lte(N,P,O1,Prob2),
        Prob is Prob1 + Prob2, !.

binom(N,_,O,0.0):- O > N, !.
binom(N,P,O,Prob):-
        choose(N,O,C),
        E1 is P^O,
        P2 is 1 - P,
        O2 is N - O,
        E2 is P2^O2,
        Prob is C*E1*E2, !.
 
choose(N,I,V):-
        NI is N-I,
        (NI > I -> pfac(N,NI,I,V) ; pfac(N,I,NI,V)).

pfac(0,_,_,1).
pfac(1,_,_,1).
pfac(N,N,_,1).
pfac(N,I,C,F):-
        N1 is N-1,
        C1 is C-1,
        pfac(N1,I,C1,N1F),
        F1 is N/C,
        F is N1F*F1.

% record_example(+Check,+Type,+Example,-N)
%	records Example of type Type
%	if Check = check, then checks to see if example exists
%		also updates number of related databases accordingly
%	if Check = nocheck then no check is done
%	returns example number N and Flag
%	if Flag = new then example is a new example of Type
record_example(check,Type,Example,N1):- 
	(once(example(N1,Type,Example)) -> true;
		record_example(nocheck,Type,Example,N1),
		(recorded(aleph,atoms(Type,Atoms),DbRef0) ->
				erase(DbRef0);
				Atoms = []),
		(recorded(aleph,atoms_left(Type,AtomsLeft),DbRef1) ->
				erase(DbRef1);
				AtomsLeft = []),
		(recorded(aleph,last_example(Type,_),DbRef2) ->
				erase(DbRef2);
				true),
		update(Atoms,N1-N1,NewAtoms),
		update(AtomsLeft,N1-N1,NewAtomsLeft),
		recorda(aleph,atoms(Type,NewAtoms),_),
		recorda(aleph,atoms_left(Type,NewAtomsLeft),_),
		recorda(aleph,last_example(Type,N1),_)),
	!.
record_example(nocheck,Type,Example,N1):-
	(recorded(aleph,size(Type,N),DbRef)->
		erase(DbRef);
		N is 0),
	N1 is N + 1,
	recorda(aleph,size(Type,N1),_),
	(Type \= neg ->
		recorded(aleph,skolemvars(Sk1),DbRef2),
		skolemize(Example,Fact,Body,Sk1,SkolemVars),
		record_skolemized(Type,N1,SkolemVars,Fact,Body),
		(Sk1 = SkolemVars -> true;
			erase(DbRef2),
			recorda(aleph,skolemvars(SkolemVars),_));
		split_clause(Example,Head,Body),
		record_nskolemized(Type,N1,Head,Body)), !.


record_targetpred:-
	recorded(aleph_dyn,backpred(Name/Arity),DbRef),
	erase(DbRef),
	recorda(aleph,targetpred(Name/Arity),_),
	record_testclause(Name/Arity),
	fail.
record_targetpred.

check_recursive_calls:-
	recorded(aleph,targetpred(Name/Arity),_),
	recorded(aleph,determination(Name/Arity,Name/Arity),_),
	record_recursive_sat_call(Name/Arity),
	fail.
check_recursive_calls.

check_posonly:-
	recorded(aleph,size(rand,N),_), 
	N > 0, !.
check_posonly:-
	setting(evalfn,posonly),
	not(recorded(aleph,modeh(_,_),_)),
	p1_message('error'),
	p_message('missing modeh declaration in posonly mode'), !,
	fail.
check_posonly:-
	retract_all(slp,_),
	setting(evalfn,posonly),
	setting(gsamplesize,S),
	condition_target,
	recorded(aleph,targetpred(Name/Arity),_),
	gsample(Name/Arity,S), !.
check_posonly.

check_prune_defs:-
	clause(prune(_),_), !,
	set(prune_defs,true).
check_prune_defs.

check_auto_refine:-
	(setting(construct_bottom,reduction);setting(construct_bottom,false)),
	not(setting(autorefine,true)), !,
	(setting(refine,user) -> true; set(refine,auto)).
check_auto_refine.

check_user_search:-
	setting(evalfn,user),
	not(cost_cover_required),
	set(lazy_on_cost,true), !.
check_user_search.

cost_cover_required:-
	clause(cost(_,Label,Cost),Body),
	vars_in_term([Label],[],Vars),
	(occurs_in(Vars,p(Cost)); occurs_in(Vars,Body)), !.

do_precomputation:-
	pre_compute(Rule),
	split_clause(Rule,Head,Body),
	(clause(Head,Body) -> true;
		asserta(Rule),
		p_message('pre-computation'),
		p_message(Rule)),
	fail.
do_precomputation.

set_lazy_negs(_):-
	recorded(aleph,set(lazy_negs,false),_), !.
set_lazy_negs(N):-
	N >= 100, !,
	recorda(aleph,set(lazy_negs,true),_).
set_lazy_negs(_).

set_lazy_recalls:-
	recorded(aleph,lazy_evaluate(Name/Arity),_),
	functor(Pred,Name,Arity),
	recorda(aleph,lazy_recall(Name/Arity,0),_),
	recorded(aleph,mode(Recall,Pred),_),
	recorded(aleph,lazy_recall(Name/Arity,N),DbRef),
	(Recall = '*' -> RecallNum = 100; RecallNum = Recall),
	RecallNum > N,
	erase(DbRef),
	recorda(aleph,lazy_recall(Name/Arity,RecallNum),_),
	fail.
set_lazy_recalls.

set_lazy_on_contradiction(_,_):-
	recorded(aleph,set(lazy_on_contradiction,false),_), !.
set_lazy_on_contradiction(P,N):-
	Tot is P + N,
	Tot >= 100, !,
	set(lazy_on_contradiction,true).
set_lazy_on_contradiction(_,_).

% clause for testing partial clauses obtained in search
record_testclause(Name/Arity):-
        functor(Head,Name,Arity),
        Clause = (Head:-
                        recorded(pclause,pclause(Head,Body),_),
                        Body, !),
        assertz(Clause).

% clause for incorporating recursive calls into bottom clause
% this is done by allowing calls to the positive examples
record_recursive_sat_call(Name/Arity):-
        functor(Head,Name,Arity),
	Clause = (Head:-
			recorded(aleph,set(stage,saturation),_),
			recorded(sat,sat(Num,Type),_), !,
			example(Num1,Type,Head),
			Num1 \= Num),		% to prevent tautologies
	assertz(Clause).

skolemize((Head:-Body),SHead,SBody,Start,SkolemVars):-
	!,
	copy_term((Head:-Body),(SHead:-Body1)),
	numbervars((SHead:-Body1),Start,SkolemVars),
	goals_to_list(Body1,SBody).
skolemize(UnitClause,Lit,[],Start,SkolemVars):-
	copy_term(UnitClause,Lit),
	numbervars(Lit,Start,SkolemVars).
skolemize(UnitClause,Lit):-
	skolemize(UnitClause,Lit,[],0,_).

record_nskolemized(Type,N1,Head,true):-
	!,
	assertz(example(N1,Type,Head)).
record_nskolemized(Type,N1,Head,Body):-
	assertz((example(N1,Type,Head):-Body)).

record_skolemized(Type,N1,SkolemVars,Head,Body):-
	assertz(example(N1,Type,Head)),
        functor(Head,Name,Arity),
        update_backpreds(Name/Arity),
	add_backs(Body),
	add_skolem_types(SkolemVars,Head,Body).

add_backs([]).
add_backs([Lit|Lits]):-
	recorda(aleph,back(Lit),_),
	functor(Lit,Name,Arity),
	declare_dynamic(Name/Arity),
	assertz(Lit),
	add_backs(Lits).

add_skolem_types(10000,_,_):- !.	% no new skolem variables
add_skolem_types(_,Head,Body):-
	add_skolem_types([Head]),
	add_skolem_types(Body).

add_skolem_types([]).
add_skolem_types([Lit|Lits]):-
	functor(Lit,PSym,Arity),
	get_modes(PSym/Arity,L),
	add_skolem_types1(L,Lit),
	add_skolem_types(Lits).

add_skolem_types1([],_).
add_skolem_types1([Lit|Lits],Fact):-
	split_args(Lit,_,I,O,C),
	add_skolem_types2(I,Fact),
	add_skolem_types2(O,Fact),
	add_skolem_types2(C,Fact),
	add_skolem_types1(Lits,Fact).

add_skolem_types2([],_).
add_skolem_types2([Pos/Type|Rest],Literal):-
	tparg(Pos,Literal,Arg),
	SkolemType =.. [Type,Arg],
	(recorded(aleph,back(SkolemType),_)-> true;
		recorda(aleph,back(SkolemType),_),
		asserta(SkolemType)),
	add_skolem_types2(Rest,Literal).


copy_args(_,_,Arg,Arity):-
	Arg > Arity, !.
copy_args(Lit,Lit1,Arg,Arity):-
	arg(Arg,Lit,T),
	arg(Arg,Lit1,T),
	NextArg is Arg + 1,
	copy_args(Lit,Lit1,NextArg,Arity).

index_clause((Head:-true),NextClause,(Head)):-
	!,
	recorded(aleph,last_clause(ClauseNum),DbRef1),
	erase(DbRef1),
	NextClause is ClauseNum + 1,
	recorda(aleph,last_clause(NextClause),_).
index_clause(Clause,NextClause,Clause):-
	recorded(aleph,last_clause(ClauseNum),DbRef1),
	erase(DbRef1),
	NextClause is ClauseNum + 1,
	recorda(aleph,last_clause(NextClause),_).

update_backpreds(Name/Arity):-
	recorded(aleph_dyn,backpred(Name/Arity),_), !.
update_backpreds(Name/Arity):-
	recordz(aleph_dyn,backpred(Name/Arity),_).
	
reset_counts:-
	retract_all(sat,last_term(_)),
	retract_all(sat,last_var(_)),
	recorda(sat,last_term(0),_),
	recorda(sat,last_var(0),_), !.

% reset the number of successes for a literal: cut to avoid useless backtrack
reset_succ:-
        retract_all(aleph_dyn,last_success(_)),
        recorda(aleph_dyn,last_success(0),_), !.

skolem_var(Var):-
	atomic(Var), !,
	name(Var,[36|_]).
skolem_var(Var):-
	gen_var(Num),
	name(Num,L),
	name(Var,[36|L]).

gen_var(Var1):-
	recorded(sat,last_var(Var0),DbRef), !,
	erase(DbRef),
        Var1 is Var0 + 1,
	recorda(sat,last_var(Var1),_).
gen_var(0):-
	recorda(sat,last_var(0),_).

copy_var(OldVar,NewVar,Depth):-
	gen_var(NewVar),
	recorded(vars,vars(OldVar,TNo,_,_),_),
	recorda(vars,vars(NewVar,TNo,[],[]),_),
	recorda(vars,copy(NewVar,OldVar,Depth),_).

gen_lit(Lit1):-
	recorded(sat,last_lit(Lit0),DbRef), !,
	erase(DbRef),
        Lit1 is Lit0 + 1,
	recorda(sat,last_lit(Lit1),_).
gen_lit(0):-
	recorda(sat,last_lit(0),_).

gen_refine_id(R1):-
	recorded(refine,last_refine(R0),DbRef), !,
	erase(DbRef),
	R1 is R0 + 1,
	recorda(refine,last_refine(R1),_).
gen_refine_id(0):-
	recorda(refine,last_refine(0),_).

gen_lits([],[]).
gen_lits([Lit|Lits],[LitNum|Nums]):-
	gen_lit(LitNum),
	recorda(lits,lit_info(LitNum,0,Lit,[],[],[]),_),
	gen_lits(Lits,Nums).

update_theory(ClauseIndex):-
        recorded(aleph,hypothesis(OldLabel,Hypothesis,OldPCover,OldNCover),DbRef), 
        erase(DbRef),
	index_clause(Hypothesis,ClauseIndex,Clause),
        (recorded(aleph,example_selected(_,Seed),_)-> true;
                PCover = [Seed-_|_]),
	(setting(lazy_on_cost,true) ->
		label_create(Clause,Label),
        	extract_pos(Label,PCover),
        	extract_neg(Label,NCover),
        	interval_count(PCover,PC),
        	interval_count(NCover,NC),
		OldLabel = [_,_|T],
        	recordz(aleph,theory(ClauseIndex,[PC,NC|T]/Seed,Clause,PCover,NCover),_);
        	recordz(aleph,theory(ClauseIndex,OldLabel/Seed,Clause,
					OldPCover,OldNCover),_)),
        (recorded(aleph,rules(Rules),DbRef3)->
                erase(DbRef3),
                recorda(aleph,rules([ClauseIndex|Rules]),_);
                recorda(aleph,rules([ClauseIndex]),_)),
        assertz(Clause), !.


rm_seeds:-
	update_theory(ClauseIndex), !,
	recorded(aleph,theory(ClauseIndex,_,_,PCover,NCover),_),
	rm_seeds(pos,PCover),
	(setting(evalfn,posonly) -> rm_seeds(rand,NCover); true),
	recorded(aleph,atoms_left(pos,PLeft),_),
	interval_count(PLeft,PL),
	p1_message('atoms left'), p_message(PL),
	!.
rm_seeds.

rm_seeds(Type,RmIntervals) :-
        recorded(aleph,atoms_left(Type,OldIntervals),DbRef),
        erase(DbRef),
        rm_seeds1(RmIntervals,OldIntervals,NewIntervals),
        recordz(aleph,atoms_left(Type,NewIntervals),_).
 
rm_seeds1([],Done,Done).
rm_seeds1([Start-Finish|Rest],OldIntervals,NewIntervals) :-
        rm_interval(Start-Finish,OldIntervals,MidIntervals),!,
        rm_seeds1(Rest,MidIntervals,NewIntervals).

% update lower estimate on maximum size cover set for an atom
update_coverset(Type,_):-
        recorded(aleph,hypothesis(Label,_,PCover,_),_),
	Label = [_,_,_,Gain|_],
        worse_coversets(PCover,Type,Gain,Worse),
        (Worse = [] -> true;
                update_theory(NewClause),
                update_coversets(Worse,NewClause,Type,Label)).

% revise coversets of previous atoms
worse_coversets(_,_,_,[]):-
	not(recorded(aleph,set(maxcover,true),_)), !.
worse_coversets([],_,_,[]).
worse_coversets([Interval|Intervals],Type,Gain,Worse):-
	worse_coversets1(Interval,Type,Gain,W1),
	worse_coversets(Intervals,Type,Gain,W2),
	aleph_append(W2,W1,Worse), !.

worse_coversets1(Start-Finish,_,_,[]):-
        Start > Finish, !.
worse_coversets1(Start-Finish,Type,Gain,Rest):-
        recorded(aleph,max_set(Type,Start,Label1,_),_),
	Label1 = [_,_,_,Gain1|_],
        Gain1 >= Gain, !,
        Next is Start + 1,
        worse_coversets1(Next-Finish,Type,Gain,Rest), !.
worse_coversets1(Start-Finish,Type,Gain,[Start|Rest]):-
        Next is Start + 1,
        worse_coversets1(Next-Finish,Type,Gain,Rest), !.

update_coversets([],_,_,_).
update_coversets([Atom|Atoms],ClauseNum,Type,Label):-
	(recorded(aleph,max_set(Type,Atom,_,_),DbRef)->
		erase(DbRef);
		true),
	recorda(aleph,max_set(Type,Atom,Label,ClauseNum),_),
	update_coversets(Atoms,ClauseNum,Type,Label), !.

rm_intervals([],I,I).
rm_intervals([I1|I],Intervals,Result):-
	rm_interval(I1,Intervals,Intervals1), 
	rm_intervals(I,Intervals1,Result).

rm_interval(_,[],[]).
rm_interval(I1,[Interval|Rest],Intervals):-
	interval_intersection(I1,Interval,I2), !,
	interval_subtract(Interval,I2,I3),
	rm_interval(I1,Rest,I4),
	aleph_append(I4,I3,Intervals).
rm_interval(I1,[Interval|Rest],[Interval|Intervals]):-
	rm_interval(I1,Rest,Intervals).

% gen_sample(+Type,+N)
% select N random samples from the set of examples uncovered. Type is one of pos/neg
% if N = 0 returns first example in Set
gen_sample(Type,0):-
	!,
	recorded(aleph,atoms_left(Type,[ExampleNum-_|_]),_),
	retract_all(aleph,example_selected(_,_)),
	p1_message('select example'), p_message(ExampleNum),
	recordz(aleph,example_selected(Type,ExampleNum),_).
gen_sample(Type,SampleSize):-
	recorded(aleph,atoms_left(Type,Intervals),_),
	% p1_message('select from'), p_message(Intervals),
	interval_count(Intervals,AtomsLeft),
	N is min(AtomsLeft,SampleSize),
	recordz(aleph_dyn,sample_num(0),_),
	retract_all(aleph,example_selected(_,_)),
	repeat,
	recorded(aleph_dyn,sample_num(S1),DbRef),
	S is S1 + 1,
	(S =< N ->
		get_random(AtomsLeft,INum),
		select_example(INum,0,Intervals,ExampleNum),
		not(recorded(aleph,example_selected(Type,ExampleNum),_)),
		p1_message('select example'), p_message(ExampleNum),
		erase(DbRef),
		recordz(aleph_dyn,sample_num(S),_),
		recordz(aleph,example_selected(Type,ExampleNum),_),
		fail;
		erase(DbRef)), !.

select_example(Num,NumberSoFar,[Start-Finish|_],ExampleNum):-
	Num =< NumberSoFar + Finish - Start + 1, !,
	ExampleNum is Num - NumberSoFar + Start - 1.
select_example(Num,NumberSoFar,[Start-Finish|Rest],ExampleNum):-
	N1 is NumberSoFar + Finish - Start + 1,
	select_example(Num,N1,Rest,ExampleNum).
	
% get_random(+Last,-Num)
% 	get a random integer between 1 and Last
get_random(Last,INum):-
	X is random,
	Num is X*Last,
	Num1 is Num + 0.5,
	INum1 is integer(Num1),
	(INum1 = 0 -> INum = 1; INum = INum1).

% get_rrandom(+Last,-Num)
% 	get a random floating point number between 1 and Last
get_rrandom(Last,Num):-
	X is random,
	Num is X*Last.

% distrib(+Interval,+Prob,-Distrib)
%	generate discrete distribution Distrib
%	by assigning all elements in Interval the probability Prob
distrib(X-Y,_,[]):-  X > Y, !.
distrib(X-Y,P,[P-X|D]):-
	X1 is X + 1,
	distrib(X1-Y,P,D).

% draw_element(+D,-E)
%	draw element E using distribution D
%	D is a list specifying the probability of each element E
%		in the form p1-e1, p2-e2, ... ,pn-en
%	       	proportions pi are normalised to add to 1
draw_element(D,E):-
	normalise_distribution(D,Distr),
	X is random,
	draw_element(Distr,0,X,E).

draw_element([P1-E1|T],CumProb,X,E):-
	CumProb1 is CumProb + P1,
	(X =< CumProb1 -> E = E1;
		draw_element(T,CumProb1,X,E)).

normalise_distribution(D,Distr):-
	key_sum(D,Sum),
	(Sum is 0.0 -> Distr = D;
		normalise_distribution(D,Sum,D1),
		keysort(D1,Distr)).

key_sum([],0.0).
key_sum([K1-_|T],Sum):-
	key_sum(T,S1),
	Sum is float(K1 + S1).

normalise_distribution([],_,[]).
normalise_distribution([K1-X1|T],Sum,[K2-X1|T1]):-
	K2 is K1/Sum,
	normalise_distribution(T,Sum,T1).

% random_select(-Num,+List1,-List2)
%       randomly remove an element Num from List1 to give List2
random_select(X,[X],[]):- !.
random_select(X,L,Left):-
        length(L,N),
        N > 0,
        get_random(N,I),
        remove_nth(I,L,X,Left).

% random_nselect(+Num,+List1,-List2)
%       randomly remove Num elements from List1 to give List2
random_nselect(0,_,[]):- !.
random_nselect(_,[],[]):- !.
random_nselect(N,List1,[X|List2]):-
        random_select(X,List1,Left),
        N1 is N - 1,
        random_nselect(N1,Left,List2).

% random_select_from_intervals(-Num,+IList)
% 	randomly select an element from an interval list
random_select_from_intervals(N,IList):-
	interval_count(IList,L),
	get_random(L,X),
	interval_select(X,IList,N).

% dummy pre-defined example to allow Yap to treat example/3
% as a static predicate.
example('$$dummy','$$dummy','$$dummy').


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% L A B E L S
% 
% calculation on labels

label_create(Clause,Label):-
        recorded(aleph,last_example(pos,Last1),_),
	Type1 = pos,
	(setting(evalfn,posonly) ->
        	recorded(aleph,last_example(rand,Last2),_),
		Type2 = rand;
        	recorded(aleph,last_example(neg,Last2),_),
		Type2 = neg),
	label_create(Clause,Type1,[1-Last1],Type2,[1-Last2],Label).

label_create(Type,Clause,Label):-
        recorded(aleph,last_example(Type,Last),_),
	label_create(Clause,Type,[1-Last],Label).

label_create(Clause,Type1,Set1,Type2,Set2,Label):-
        split_clause(Clause,Head,Body),
	nlits((Head,Body),Length),
        recordz(pclause,pclause(Head,Body),DbRef),
        recorded(aleph,set(depth,Depth),_),
	(recorded(aleph,set(prooftime,Time),_) -> true; Time = inf),
        prove(Depth/Time,Type1,(Head:-Body),Set1,Cover1,_),
        prove(Depth/Time,Type2,(Head:-Body),Set2,Cover2,_),
        erase(DbRef),
        assemble_label(Cover1,Cover2,Length,Label), !.

label_create(Clause,Type,Set,Label):-
        split_clause(Clause,Head,Body),
        recordz(pclause,pclause(Head,Body),DbRef),
        recorded(aleph,set(depth,Depth),_),
	(recorded(aleph,set(prooftime,Time),_) -> true; Time = inf),
        prove(Depth/Time,Type,(Head:-Body),Set,Cover,_),
        erase(DbRef),
	(Type = pos -> 
        	assemble_label(Cover,unknown,unknown,Label);
        	assemble_label(unknown,Cover,unknown,Label)).

label_pcover(Label,P):-
	extract_cover(pos,Label,P).
label_ncover(Label,N):-
	extract_cover(neg,Label,N).

label_union([],Label,Label):- !.
label_union(Label,[],Label):- !.
label_union(Label1,Label2,Label):-
        extract_cover(pos,Label1,Pos1),
        extract_cover(pos,Label2,Pos2),
        extract_cover(neg,Label1,Neg1),
        extract_cover(neg,Label2,Neg2),
        extract_length(Label1,L1),
        extract_length(Label2,L2),
        update_list(Pos2,Pos1,Pos),
        update_list(Neg2,Neg1,Neg),
        Length is L1 + L2,
        list_to_intervals(Pos,PCover),
        list_to_intervals(Neg,NCover),
        assemble_label(PCover,NCover,Length,Label).

label_print([]):- !.
label_print(Label):-
	Eval = coverage,
	evalfn(Eval,Label,Val),
	print_eval(Eval,Val).

print_eval(Evalfn,Val):-
	evalfn_name(Evalfn,Name),
	(Evalfn = user -> Value is -Val; Value is Val),
	p1_message(Name), p_message(Value).


eval_rule(0,Label):-
	recorded(aleph,hypothesis(_,Clause,_,_),_), !,
	label_create(Clause,Label),
	p_message('Rule 0'),
	pp_dclause(Clause),
	extract_count(pos,Label,PC),
	extract_count(neg,Label,NC),
	extract_length(Label,L),
	label_print([PC,NC,L]),
	nl.
eval_rule(ClauseNum,Label):-
	integer(ClauseNum),
	ClauseNum > 0,
	recorded(aleph,theory(ClauseNum,_,Clause,_,_),_),
	!,
	label_create(Clause,Label),
	extract_count(pos,Label,PC),
	extract_count(neg,Label,NC),
	concat(['Rule ',ClauseNum],RuleTag),
	(setting(evalfn,posonly) ->
		concat(['Pos cover = ',PC,' Rand cover = ',NC],CoverTag);
		concat(['Pos cover = ',PC,' Neg cover = ',NC],CoverTag)),
	p1_message(RuleTag), p_message(CoverTag),
	pp_dclause(Clause),
	nl.
eval_rule(_,_).


evalfn(Label,Val):-
	(setting(evalfn,Eval)->true;Eval=coverage),
	evalfn(Eval,Label,Val).

evalfn_name(compression,'compression').
evalfn_name(coverage,'pos-neg').
evalfn_name(pcoverage,'pos').
evalfn_name(accuracy,'accuracy').
evalfn_name(laplace,'laplace estimate').
evalfn_name(pbayes,'pseudo-bayes estimate').
evalfn_name(auto_m,'m estimate').
evalfn_name(mestimate,'m estimate').
evalfn_name(posonly,'posonly bayes estimate').
evalfn_name(user,'user defined cost').

evalfn(compression,[P,N,L|_],Val):-
	(P = -inf -> Val = -10000.0;
        	Val is P - N - L + 1), !.
evalfn(coverage,[P,N,_|_],Val):-
	(P = -inf -> Val = -10000;
		Val is P - N), !.
evalfn(pcoverage,[P,_,_|_],Val):-
	(P = -inf -> Val = -10000;
		Val is P), !.
evalfn(laplace,[P,N,_|_],Val):-
	(P = -10000 -> Val = 0.5;
		Val is (P + 1) / (P + N + 2)), !.
evalfn(accuracy,[P,N,_|_],Val):-
	(P = -10000 -> Val = 0.5;
		Val is P / (P + N)), !.
% the evaluation functions below are due to James Cussens
evalfn(pbayes,[P,N,_|_],Val):-
        (P = -10000 -> Val = 0.5;
                Acc is P/(P+N),
                setting(prior,Prior),
                (0 is Prior-Acc ->
                    Val=Prior;
                K is (Acc*(1 - Acc)) / ((Prior-Acc)^2 ),
                Val is (P + K*Prior) / (P + N + K))), !.
evalfn(MEst,[P,N,_|_],Val):-
        (MEst = auto_m; MEst = mestimate),
        (P = -10000 -> Val = 0.5;
                Cover is P + N,
                setting(prior,Prior),   
                (MEst = auto_m -> K is sqrt(Cover);
                        (setting(m,M) -> K = M; K is sqrt(Cover))),
                Val is (P + K*Prior) / (Cover+K)), !.
evalfn(_,_,-10000).


assemble_label(P,N,L,[P,N,L]).

extract_cover(pos,[P,_,_],P1):-
        intervals_to_list(P,P1), !.
extract_cover(neg,[_,N,_],N1):-
        intervals_to_list(N,N1),!.
extract_cover(_,[]).

extract_count(pos,[P,_,_],P1):-
	interval_count(P,P1), !.
extract_count(neg,[_,N,_],N1):-
	interval_count(N,N1), !.
extract_count(neg,_,0).


extract_pos([P,_,_],P).
extract_neg([_,N,_],N).
extract_length([_,_,L],L).

get_start_label(_,[0,0,0,-10000]):-
	setting(mode,incremental), !.
get_start_label(user,[1,0,2,-10000]):- !.
get_start_label(posonly,[1,0,2,-1,0]):- !.
get_start_label(Evalfn,[1,0,2,Val]):-
	evalfn(Evalfn,[1,0,2],Val).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% I / O   S T U F F

read_all(Prefix):-
	clean_up,
	reset,
	set(prefix,Prefix),
	read_background(Prefix),
	read_examples(Prefix), 	
	record_targetpred, 	
	check_recursive_calls,
	check_prune_defs,
	check_user_search,
	do_precomputation,
	check_posonly,
	check_auto_refine,
	show(settings).


read_background(Prefix):-
	retract_all(aleph,mode(_,_)),
	retract_all(aleph,determination(_,_)),
	construct_name(Prefix,rules,File),
	reconsult(File).

read_examples(Prefix):-
	(setting(skolemvars,SkVars) -> true; SkVars = 10000),
	recorda(aleph,skolemvars(SkVars),_), % hack: var numbers after this are skolem
	read_examples(pos,Prefix),
	read_examples(neg,Prefix),
	recorded(aleph,size(pos,P),_),
	recorded(aleph,size(neg,N),_),
	(P > 0 -> PosE = [1-P]; PosE = []),
	(N > 0 -> NegE = [1-N]; NegE = []),
	recorda(aleph,atoms(pos,PosE),_),
	recorda(aleph,atoms_left(pos,PosE),_),
	recorda(aleph,atoms(neg,NegE),_),
	recorda(aleph,atoms_left(neg,NegE),_),
	recorda(aleph,last_example(pos,P),_),
	recorda(aleph,last_example(neg,N),_),
	set_lazy_recalls,
	% set_lazy_on_contradiction(P,N),
	(setting(prior,_) -> true; Prior is P/(P+N), set(prior,Prior)),
	reset_counts,
	recorda(aleph,last_clause(0),_).

read_examples(Type,Prefix):-
	retract_all(aleph,size(Type,_)),
	recorda(aleph,size(Type,0),_),
	construct_name(Prefix,Type,File),
	(Type = pos -> Flag = train_pos; Flag = train_neg),
	set(Flag,File),
	(open(File,read,Stream) ->
		p1_message(consulting),
		concat([Type, ' examples'],Mess),
		p_message(Mess);
		p1_message('cannot open'), p_message(File),
		fail),
	repeat,
	read(Stream,Example),
	(Example=end_of_file-> close(Stream);
		record_example(nocheck,Type,Example,_),
		fail),
	!.
read_examples(_,_).

construct_name(Prefix,Type,Name):-
	name(Prefix,PString),
	suffix(Type,SString),
	aleph_append(SString,PString,FString),
	name(Name,FString).

construct_prolog_name(Name,Name):-
	name('.pl',Suffix),
	name(Name,Str),
	aleph_append(Suffix,_,Str), !.
construct_prolog_name(Name,Name1):-
	name(Name,Str),
	name('.pl',Suffix),
	aleph_append(Suffix,Str,Name1Str),
	name(Name1,Name1Str).

suffix(pos,Suffix):- name('.f',Suffix).
suffix(neg,Suffix):- name('.n',Suffix).
suffix(rules,Suffix):- name('.b',Suffix).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% L I B R A R Y

execute(C):-
	system(C), !.
execute(_).

% store critical values of current search state
store(searchstate):-
	!,
	retract_all(aleph,save(searchstate,_)),
	(recorded(aleph,atoms_left(pos,PosLeft),_) ->
		recorda(aleph,save(searchstate,atoms_left(pos,PosLeft)),_);
		true),
	(recorded(aleph,atoms_left(neg,NegLeft),_) ->
		recorda(aleph,save(searchstate,atoms_left(neg,NegLeft)),_);
		true),
	(recorded(aleph,size(pos,PSize),_) ->
		recorda(aleph,save(searchstate,size(pos,PSize)),_);
		true),
	(recorded(aleph,size(neg,NSize),_) ->
		recorda(aleph,save(searchstate,size(neg,NSize)),_);
		true),
	(recorded(aleph,set(noise,Noise),_) ->
		recorda(aleph,save(searchstate,set(noise,Noise)),_);
		true),
	(recorded(aleph,set(minacc,MinAcc),_) ->
		recorda(aleph,save(searchstate,set(minacc,MinAcc)),_);
		true).

% store current bottom clause
store(bottom):-
	!,
	(recorded(aleph,set(store_bottom,true),_) ->
		store_bottom;
		true).


store(Parameter):-
	(recorded(aleph,set(Parameter,Value),_) -> true; Value = unknown),
	retract_all(aleph,save(Parameter,_)),
	recorda(aleph,save(Parameter,Value),_).

% store values of a list of parameters
store_values([]).
store_values([Parameter|T]):-
	store(Parameter),
	store_values(T).

% store all relevant info related to current bottom
%	details are stored in 5 idbs:
%	1. bottom: points to 2 other idbs sat_X_n and lits_X_N
%	2. sat_X_N: where X is the type of the current example and N the number 
%		this contains misc stuff recorded by sat/2 for use by reduce/1
%	3. lits_X_N: contains the lits in bottom
%	4. ovars_X_N: contains output vars of lits in bottom
%	5. ivars_X_N: contains input vars of lits in bottom
store_bottom:-
	bottom_keys(Num,Type,Keys,true),
	recorda(bottom,stored(Num,Type,Keys),_),
	arg(1,Keys,K1), arg(2,Keys,K2),
	arg(3,Keys,K3), arg(4,Keys,K4),
	recorded(sat,last_term(LastTerm),_),
	recorda(K1,last_term(LastTerm),_),
	recorded(sat,last_var(LastVar),_),
	recorda(K1,last_var(LastVar),_),
	recorded(sat,bot_size(BotSize),_),
	recorda(K1,bot_size(BotSize),_),
	recorded(sat,last_lit(LastLit),_),
	recorda(K1,last_lit(LastLit),_),
	recorded(sat,head_ovars(HOVars),_),
	recorda(K1,head_ovars(HOVars),_),
	recorded(sat,head_ivars(HIVars),_),
	recorda(K1,head_ivars(HIVars),_),
	recorded(sat,set(eq,Eq),_),
	recorda(K1,set(eq,Eq),_),
	recorded(lits,lit_info(Lit,Depth,Atom,I,O,D),_),
	recorda(K2,lit_info(Lit,Depth,Atom,I,O,D),_),
	get_ovars1(Lit,K3,K2,OVars),
	recorda(K3,ovars(Lit,OVars),_),
	get_ivars1(Lit,K4,K2,OVars),
	recorda(K4,ivars(Lit,OVars),_),
	fail.
store_bottom.
	

reinstate(searchstate):-
	!,
	retract_all(aleph,atoms_left(_,_)),
	retract_all(aleph,size(_,_)),
	(recorded(aleph,save(searchstate,atoms_left(pos,PosLeft)),_) ->
		recorda(aleph,atoms_left(pos,PosLeft),_);
		true),
	(recorded(aleph,save(searchstate,atoms_left(neg,NegLeft)),_) ->
		recorda(aleph,atoms_left(neg,NegLeft),_);
		true),
	(recorded(aleph,save(searchstate,size(pos,PSize)),_) ->
		recorda(aleph,size(pos,PSize),_);
		true),
	(recorded(aleph,save(searchstate,size(neg,NSize)),_) ->
		recorda(aleph,size(neg,NSize),_);
		true),
	(recorded(aleph,save(searchstate,set(noise,Noise)),_) ->
		set(noise,Noise);
		true),
	(recorded(aleph,save(searchstate,set(minacc,MinAcc)),_) ->
		set(minacc,MinAcc);
		true),
	retract_all(aleph,save(searchstate,_)).
reinstate(Parameter):-
	recorded(aleph,save(Parameter,Value),DbRef), !,
	erase(DbRef),
	(Value = unknown -> noset(Parameter); set(Parameter,Value)).
reinstate(_).

% reinstate list of values of parameters
reinstate_values([]).
reinstate_values([Parameter|T]):-
	reinstate(Parameter),
	reinstate_values(T).

% reinstate all saved values
reinstate_values:-
	recorded(aleph,save(_,_),_), 
	repeat,
	recorded(aleph,save(Parameter,Value),DbRef), 
	erase(DbRef),
	(Value = unknown -> noset(Parameter) ; set(Parameter,Value)),
	not(recorded(aleph,save(_,_),_)),
	!.
reinstate_values.

% bottom_keys(?N,?T,-Keys,-Flag)
%	returns idb keys that store bottom clause info for example N of type T
%	Flag is one of "true" or "false" depending on whether bottom
%	requires storing
bottom_keys(N,T,Keys,Flag):-
	recorded(sat,sat(N,T),_),
	(setting(store_bottom,true) ->
		(recorded(bottom,stored(N,T,Keys),_) ->
			Flag = false;
			concat([sat,'_',T,'_',N],S),
			concat([lits,'_',T,'_',N],L),
			concat([ovars,'_',T,'_',N],O),
			concat([ivars,'_',T,'_',N],I),
			Flag = true,
			Keys = keys(S,L,O,I)
		);
		S = sat, L = lits, O = ovars, I = ivars,
		Flag = false,
		Keys = keys(S,L,O,I)).

set(Variable,Value):-
	var(Value), !,
	recorded(aleph,set(Variable,Value),_).
set(Variable,Value):-
	noset(Variable),
	recordz(aleph,set(Variable,Value),_),
	special_consideration(Variable,Value).

setting(Variable,Value):-
	recorded(aleph,set(Variable,Value),_).

noset(Variable):-
        recorded(aleph,set(Variable,Value),DbRef), !,
	erase(DbRef), 
	rm_special_consideration(Variable,Value).
noset(_).

man(M):-
	aleph_manual(M).

determinations(Pred1,Pred2):-
        recorded(aleph,determination(Pred1,Pred2),_).

determination(Pred1,Pred2):-
	noset(autorefine),
	recordz(aleph,determination(Pred1,Pred2),_).

commutative(Pred):-
	recordz(aleph,commutative(Pred),_).

symmetric(Pred):-
	set(check_symmetry,true),
	recordz(aleph,symmetric(Pred),_).

lazy_evaluate(Name/Arity):-
        recordz(aleph,lazy_evaluate(Name/Arity),_).

positive_only(Pred):-
	recordz(aleph,positive_only(Pred),_).

mode(Recall,Pred):-
	recordz(aleph,modeb(Recall,Pred),_),
	recordz(aleph,mode(Recall,Pred),_),
	noset(autorefine).

modes(N/A,Mode):-
	Mode = modeh(_,Pred),
	recorded(aleph,Mode,_),
	functor(Pred,N,A).
modes(N/A,Mode):-
	Mode = modeb(_,Pred),
	recorded(aleph,Mode,_),
	functor(Pred,N,A).

modeh(Recall,Pred):-
	(recorded(aleph,mode(Recall,Pred),_) -> true;
		noset(autorefine),
		recordz(aleph,modeh(Recall,Pred),_),
		recordz(aleph,mode(Recall,Pred),_),
        	functor(Pred,Name,Arity),
        	update_backpreds(Name/Arity)).
modeb(Recall,Pred):-
	(recorded(aleph,modeb(Recall,Pred),_) -> true;
		noset(autorefine),
		recordz(aleph,modeb(Recall,Pred),_),
		(recorded(aleph,mode(Recall,Pred),_) -> true;
			recordz(aleph,mode(Recall,Pred),_))).

show(settings):-
	nl,
	p_message('settings'),
	findall(P-V,setting(P,V),L),
	sort(L,L1),
	aleph_member(Parameter-Value,L1),
        tab(8), write(Parameter=Value), nl,
        fail.
show(determinations):-
	nl,
	p_message('determinations'),
	show1(aleph,determination(_,_)).
show(modes):-
	nl,
	p_message('modes'),
	show1(aleph,mode(_,_)).
show(modehs):-
	nl,
	p_message('modehs'),
	show1(aleph,modeh(_,_)).
show(modebs):-
	nl,
	p_message('modebs'),
	show1(aleph,modeb(_,_)).
show(sizes):-
	nl,
	p_message('sizes'),
	show1(aleph,size(_,_)).
show(bottom):-
	nl,
	p_message('bottom clause'),
	set(verbosity,V),
	V > 0,
	recorded(sat,last_lit(Last),_),
	get_clause(1,Last,[],FlatClause),
	pp_dlist(FlatClause).
show(theory):-
        nl,
        p_message('theory'),
        nl,
        recorded(aleph,rules(L),_),
        aleph_reverse(L,L1),
        aleph_member(ClauseNum,L1),
	recorded(aleph,theory(ClauseNum,_,_,_,_),_),
	eval_rule(ClauseNum,_),
	% pp_dclause(Clause),
        fail.
show(theory):-
	get_performance.
show(pos):-
	nl,
	p_message('positives'),
	store(greedy),
	examples(pos,_),
	reinstate(greedy),
	fail.
show(neg):-
	nl,
	p_message('negatives'),
	store(greedy),
	examples(neg,_),
	reinstate(greedy),
	fail.
show(rand):-
	nl,
	p_message('random'),
	examples(rand,_),
	fail.
show(uspec):-
	nl,
	p_message('uspec'),
	examples(uspec,_),
	fail.
show(prior):-
	nl,
	p_message('refinement priors'),
	beta(Refine,A,B),
	copy_term(Refine,Refine1),
% ICD:	numbervars(Refine1,0,_),
	numbervars_nosingletons(Refine1,0,_),
	write(beta(Refine1,A,B)), write('.'), nl,
	fail.
show(posterior):-
	nl,
	p_message('refinement posterior'),
	recorded(refine,beta(R,A,B),_),
	recorded(refine,refine_id(Refine,R),_),
	copy_term(Refine,Refine1),
% ICD:	numbervars(Refine1,0,_),
	numbervars_nosingletons(Refine1,0,_),
	write(beta(Refine1,A,B)), write('.'), nl,
	fail.
show(gcws):-
	nl,
	p_message('gcws hypothesis'),
	recorded(gcws,hypothesis(_,C,_,_),_),
	pp_dclause(C),
	fail.
show(hypothesis):-
	aleph_portray(hypothesis),
	fail.
show(search):-
	aleph_portray(search).
show(good):-
        nl,
        p_message('good clauses'),
        setting(evalfn,Evalfn),
        recorded(good,good(Label,Clause),_),
        Label = [_,_,_,F|_],
        (setting(good_score,FMin) -> F >= FMin; true),
        pp_dclause(Clause),
        show_stats(Evalfn,Label),
        fail.
show(constraints):-
        nl,
	p_message(constraints),
	listing(false).
show(prunes):-
        nl,
        p_message(prunes),
        listing(prune).
show(_).


settings:-
	show(settings).


examples(Type,List):-
        example(Num,Type,Atom),
        aleph_member1(Num,List),
        write(Atom), write('.'), nl,
        fail.
examples(_,_).


write_rules(File):-
        open(File,write,Stream),
        set_output(Stream),
	show(theory),
        close(Stream),
        set_output(user_output).
write_rules(_).

best_hypothesis(Head1,Body1,[P,N,L]):-
	recorded(search,selected([P,N,L|_],Clause,_,_),_),
	split_clause(Clause,Head2,Body2), !,
	Head1 = Head2, Body1 = Body2.

hypothesis(Head1,Body1,Label):-
	recorded(pclause,pclause(Head2,Body2),_), !,
	Head1 = Head2, Body1 = Body2,
	get_hyp_label((Head2:-Body2),Label).
hypothesis(Head1,Body1,Label):-
        recorded(aleph,hypothesis(_,Theory,_,_),_),
	(Theory = [_|_] -> aleph_member(Clause,Theory);
		Theory = Clause),
	split_clause(Clause,Head2,Body2), 
	Head1 = Head2, Body1 = Body2,
	get_hyp_label((Head2:-Body2),Label).

rdhyp:-
	retract_all(pclause,pclause(_,_)),
	retract_all(covers,covers(_,_)),
        read(Clause),
        add_hyp(Clause),
        nl,
        show(hypothesis).

addhyp:-
	recorded(aleph,hypothesis(Label,Theory,PCover,NCover),_),
	Theory = [_|_], !,
	add_theory(Label,Theory,PCover,NCover).
addhyp:-
        recorded(aleph,hypothesis(Label,_,PCover,_),_), !,   
        rm_seeds,
        worse_coversets(PCover,pos,Label,Worse),
        recorded(aleph,last_clause(NewClause),_),
        (Worse = [] -> true;
                update_coversets(Worse,NewClause,pos,Label)), !.
addhyp:-
        recorded(search,selected(Label,RClause,PCover,NCover),_), !,
        add_hyp(Label,RClause,PCover,NCover),
        rm_seeds,
        worse_coversets(PCover,pos,Label,Worse),
        recorded(aleph,last_clause(NewClause),_),
        (Worse = [] -> true;
                update_coversets(Worse,NewClause,pos,Label)), !.


% specialise a hypothesis by recursive construction of
% abnormality predicates
sphyp:-
        retract_all(specialise,_),
        retract_all(gcws,_),
        recorded(aleph,hypothesis([P,N,L|T],Clause,PCover,NCover),DbRef),
        erase(DbRef),
        recorda(specialise,hypothesis([P,N,L|T],Clause,PCover,NCover),_),
        store(searchstate),
        gcws,
        retract_all(aleph,hypothesis(_,_,_,_)),
        recorda(aleph,hypothesis([P,N,L|T],Clause,PCover,NCover),_),
        reinstate(searchstate).

addgcws:-
        recorded(gcws,hypothesis(Label,C,P,N),DbRef), !,   
	erase(DbRef),
	recorda(aleph,hypothesis(Label,C,P,N),_),
	addhyp,
	add_gcws.

rmhyp:-
        recorded(pclause,pclause(Head,Body),DbRef),
        erase(DbRef),
        recorda(aleph_dyn,tmpclause(Head,Body),_), !.
rmhyp:-
        recorded(aleph,hypothesis(Label,Clause1,P,N),DbRef),
        erase(DbRef),
        recorda(aleph_dyn,tmphypothesis(Label,Clause1,P,N),_), !.
rmhyp.


covers:-
        get_hyp(Hypothesis),
        label_create(Hypothesis,Label),
        extract_cover(pos,Label,P),
        examples(pos,P),
	length(P,PC),
	p1_message('examples covered'),
	p_message(PC),
	retract_all(covers,covers(_,_)),
	recorda(covers,covers(P,PC),_).
coversn:-
        get_hyp(Hypothesis),
        label_create(Hypothesis,Label),
        extract_cover(neg,Label,N),
        examples(neg,N),
	length(N,NC),
	p1_message('examples covered'),
	p_message(NC),
	retract_all(covers,coversn(_,_)),
	recorda(covers,coversn(N,NC),_).

% as in covers, but first checks if being done
% within a greedy search
covers(P):-
	get_hyp(Hypothesis),
	(setting(greedy,true) -> 
		recorded(aleph,atoms_left(pos,Pos),_);
		recorded(aleph,atoms(pos,Pos),_)),
	label_create(Hypothesis,pos,Pos,Label),
	retract_all(covers,covers(_,_)),
	extract_pos(Label,PCover),
	interval_count(PCover,P),
	recorda(covers,covers(PCover,P),_).

% as in coversn, but first checks if being done
% within a greedy search
coversn(N):-
	get_hyp(Hypothesis),
	(setting(greedy,true) ->
		recorded(aleph,atoms_left(neg,Neg),_);
		recorded(aleph,atoms(neg,Neg),_)),
	label_create(Hypothesis,neg,Neg,Label),
	retract_all(covers,coversn(_,_)),
	extract_neg(Label,NCover),
	interval_count(NCover,N),
	recorda(covers,coversn(NCover,N),_).

example_saturated(Example):-
	recorded(sat,sat(Num,Type),_),
	example(Num,Type,Example).


reset:-
        clean_up,
        retract_all(cache,_),
        retract_all(prune_cache,_),
        set(stage,command),
	set(construct_bottom,saturation),
	set(check_useless,false),
	set(check_redundant,false),
	set(refineop,false),
        set(lazy_on_cost,false),
        set(nodes,5000),
        set(samplesize,1),
        set(minpos,1),
        set(gsamplesize,100),
        set(clauselength,4),
        set(explore,false),
        set(caching,false),
        set(refine,false),
	set(proof_strategy,restricted_sld),
	set(computation_rule,leftmost),
        set(search,bf),
        set(prune_defs,false),
        set(evalfn,coverage),
        set(depth,10),
        set(verbosity,1),
        set(i,2),
        set(noise,0),
        set(print,4),
	set(splitvars,false),
	!.
	
time(P,N,AvTime):-
        Start is cputime,
        time_loop(N,P),
        Stop is cputime,
        Time is Stop - Start,
        AvTime is Time/N.
        
 
list_profile :-
	% get number of calls for each profiled procedure
	findall(D-P,profile_data(P,calls,D),LP),
	% sort them
	sort(LP,SLP),
	% and output (note the most often called predicates will come last
	write_profile_data(SLP).

test(File,Flag,N,T):-
	open(File,read,Stream), !,
	retract_all(aleph_dyn,covered(_)),
	retract_all(aleph_dyn,total(_)),
	recorda(aleph_dyn,covered(0),_),
	recorda(aleph_dyn,total(0),_),
	repeat,
	read(Stream,Fact),
	(Fact = end_of_file -> close(Stream);
		recorded(aleph_dyn,total(T0),DbRef),
		erase(DbRef),
		T1 is T0 + 1,
		recorda(aleph_dyn,total(T1),_),
%		(once(Fact) ->
% ICD: changed for the nuclear smuggling
	        (once((Fact = linked(A,B) -> (linked(A,B);linked(B,A));
                                             (Fact))) ->
			(Flag = show ->
				p1_message(covered),
				aleph_portray(Fact),
				nl;
				true);
			(Flag = show ->
				p1_message('not covered'),
				aleph_portray(Fact),
				nl;
				true),
			fail),
		recorded(aleph_dyn,covered(N0),DbRef1),
		erase(DbRef1),
		N1 is N0 + 1,
		recorda(aleph_dyn,covered(N1),_),
		fail),
	!,
	recorded(aleph_dyn,covered(N),DbRef2),
	erase(DbRef2),
	recorded(aleph_dyn,total(T),DbRef3),
	erase(DbRef3).
test(File,_,0,0):-
	p1_message('cannot open'), p_message(File).

in(false,_):-
	!,
	fail.
in(bottom,Lit):-
	!,
        recorded(sat,last_lit(Last),_),
        get_clause(1,Last,[],FlatClause),
	aleph_member(Lit,FlatClause).
in((Head:-true),Head):- !.
in((Head:-Body),L):-
	!,
	in((Head,Body),L).
in((L1,_),L1).
in((_,R),L):-
	!,
	in(R,L).
in(L,L).
	


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% L I B R A R Y   S U P P O R T
%
% auxilliary definitions  for lib

special_consideration(noise,_):-
        noset(minacc), !.
special_consideration(minacc,_):-
        noset(noise), !.

% the following needed for compatibility with P-Progol
special_consideration(search,ida):-
	set(search,bf), set(evalfn,coverage), !.
special_consideration(search,compression):-
	set(search,heuristic), set(evalfn,compression), !.
special_consideration(search,posonly):-
	set(search,heuristic), set(evalfn,posonly), !.
special_consideration(search,user):-
	set(search,heuristic), set(evalfn,user), !.
special_consideration(verbose,N):-
        set(verbosity,N), !.

special_consideration(caching,true):-
	(setting(cache_clauselength,_)->true;set(cache_clauselength,3)).

special_consideration(search,bf):-
	(setting(evalfn,_) -> true; set(evalfn,coverage)), !.
special_consideration(search,df):-
	(setting(evalfn,_) -> true; set(evalfn,coverage)), !.
special_consideration(search,heuristic):-
	(setting(evalfn,_)->true; set(evalfn,compression)), !.
special_consideration(evalfn,coverage):-
	(setting(search,_)->true; set(search,bf)).
special_consideration(evalfn,S):-
	(setting(search,_)->true; set(search,heuristic)),
	(S = posonly -> noset(noise);
		recorded(aleph,atoms(neg,NegE),_),
		recorded(aleph,atoms_left(neg,[]),DbRef),
		erase(DbRef),
		reinstate(noise),
		recorda(aleph,atoms_left(neg,NegE),_)).

special_consideration(refine,auto):-
	gen_auto_refine,
	set(refineop,true), !.
special_consideration(refine,probabilistic):-
	set(caching,true),
	gen_auto_refine, !.
special_consideration(refine,Refine):-
	Refine \= false, !,
	set(refineop,true).
special_consideration(construct_bottom,reduction):-
	(setting(lazy_bottom,true) -> true; set(lazy_bottom,true)), !.
special_consideration(construct_bottom,saturation):-
	noset(lazy_bottom), !.
special_consideration(lazy_bottom,true):-
	(setting(construct_bottom,false) -> true; set(construct_bottom,reduction)), !.
special_consideration(lazy_bottom,false):-
	(setting(construct_bottom,false) -> true; set(construct_bottom,saturation)), !.
special_consideration(portray_literals,true):-
	set(print,1), !.
special_consideration(_,_).

rm_special_consideration(caching,true):-
	noset(cache_clauselength), !.
rm_special_consideration(portray_literals,_):-
	set(print,4), !.
rm_special_consideration(verbose,_):-
	noset(verbosity), !.
rm_special_consideration(refine,_):-
	set(refineop,false), !.
rm_special_consideration(lazy_bottom,true):-
	(setting(refine,auto) -> set(refine,false); true), !.
rm_special_consideration(_,_).

show(Area,Name/Arity):-
        functor(Pred,Name,Arity),
        show1(Area,Pred).
show(_,_).

get_hyp((Head:-Body)):-
	recorded(pclause,pclause(Head,Body),_), !.
get_hyp(Hypothesis):-
        recorded(aleph,hypothesis(_,Hypothesis,_,_),_).

add_hyp(end_of_file):- !.
add_hyp(Clause):-
        nlits(Clause,L),
	label_create(Clause,Label),
        extract_count(pos,Label,PCount),
        extract_count(neg,Label,NCount),
        Label1 = [PCount,NCount,L],
        retract_all(aleph,hypothesis(_,_,_,_)),
        extract_pos(Label,P),
        extract_neg(Label,N),
        recorda(aleph,hypothesis(Label1,Clause,P,N),_).

add_hyp(Label,Clause,P,N):-
        retract_all(aleph,hypothesis(_,_,_,_)),
        recorda(aleph,hypothesis(Label,Clause,P,N),_).

add_theory(_,Theory,_,_):-
        aleph_member(C,Theory),
        index_clause(C,ClauseIndex,Clause),
        (recorded(aleph,rules(Rules),DbRef)->
                erase(DbRef),
                recorda(aleph,rules([ClauseIndex|Rules]),_);
                recorda(aleph,rules([ClauseIndex]),_)),
        assertz(Clause),
        fail.
add_theory(_,_,PCover,NCover):-
        recorded(aleph,atoms_left(pos,Pos),DbRef1),
        rm_intervals(PCover,Pos,Pos1),
        erase(DbRef1),
        recorda(aleph,atoms_left(pos,Pos1),_),
	(setting(evalfn,posonly) ->
        	recorded(aleph,atoms_left(rand,Rand),DbRef2),
        	rm_intervals(NCover,Rand,Rand1),
        	erase(DbRef2),
        	recorda(aleph,atoms_left(rand,Rand1),_);
        	recorded(aleph,atoms_left(neg,Neg),DbRef2),
        	rm_intervals(NCover,Neg,Neg1),
        	erase(DbRef2),
        	recorda(aleph,atoms_left(neg,Neg1),_)).
add_gcws:-
	recorded(gcws,hypothesis(L,C,P,N),DbRef),
	erase(DbRef),
	recorda(aleph,hypothesis(L,C,P,N),_),
	update_theory(_),
	fail.
add_gcws.


restorehyp:-
	recorded(aleph_dyn,tmpclause(Head,Body),DbRef),
	erase(DbRef),
	recordz(pclause,pclause(Head,Body),_), !.
restorehyp:-
	recorded(aleph_dyn,tmphypothesis(Label,Clause1,P,N),DbRef),
	erase(DbRef),
        recorda(aleph,hypothesis(Label,Clause1,P,N),_), !.
restorehyp.

get_hyp_label(_,Label):- var(Label), !.
get_hyp_label((_:-Body),[P,N,L]):-
        nlits(Body,L1),
        L is L1 + 1,
        (recorded(covers,covers(_,P),_)-> true;
                        covers(_),
                        recorded(covers,covers(_,P),_)),
        (recorded(covers,coversn(_,N),_)-> true;
                        coversn(_),
                        recorded(covers,coversn(_,N),_)).
 

show1(Area,Pred):-
        recorded(Area,Pred,_),
% ICD:  copy_term(Pred,Pred1), numbervars(Pred1,0,_),
        copy_term(Pred,Pred1), numbervars_nosingletons(Pred1,0,_),
        writeq(Pred1), write('.'), nl,
        fail.
show1(_,_).

aleph_portray(hypothesis):-
	setting(portray_hypothesis,true),
	portray(hypothesis), !.
aleph_portray(hypothesis):- 
	p_message('hypothesis'),
	hypothesis(Head,Body,_),
	pp_dclause((Head:-Body)).
aleph_portray(hypothesis):-  !.

aleph_portray(search):-
	setting(portray_search,true),
	portray(search), !.
aleph_portray(search):- !.

aleph_portray(Lit):-
	recorded(aleph,set(portray_literals,true),_),
	portray(Lit), !.
aleph_portray(Lit):-
        writeq(Lit).

aleph_portray(true,Lit):-
	portray(Lit), !.
aleph_portray(_,Lit):-
        writeq(Lit).

time_loop(0,_):- !.
time_loop(N,P):-
        P,
        N1 is N - 1,
        time_loop(N1,P).

write_profile_data([]).
        write_profile_data([D-P|SLP]) :-
        % just swap the two calls to get most often called predicates first.
        format('~w: ~w~n', [P,D]),
        write_profile_data(SLP).
 


clear_hyp:-
        retract_all(aleph,hypothesis(_,_,_,_)).

%
% use the fact that $VAR(-1) is written as _ to obtain a nicer
% output.
%
% adds a factor linear on the number of variables to numbervars/3' complexity.
%
numbervars_nosingletons(T, M, N) :-
	numbervars_nosingletons(T, M, N, Lf, []),
	number_singletons(Lf).

%
% idea: first time if find a var just put $VAR(A). Second time, bind A
% to var number.
%
numbervars_nosingletons(V, M, M, [A|L0], L0) :- var(V), !,
	V = '$VAR'(A).
numbervars_nosingletons('$VAR'(M), M, N, L0, L0) :- !,
	N is M+1.
numbervars_nosingletons('$VAR'(_), M, M, L0, L0) :- !.
numbervars_nosingletons(Atomic, M, M, L0, L0) :-
	atomic(Atomic), !.
numbervars_nosingletons(Term, M, N, LF, L0) :-
	functor(Term, _, Arity),
	numbervars_nosingletons(0,Arity, Term, M, N, LF, L0).

numbervars_nosingletons(A, A, _, N, N, L, L) :- !.
numbervars_nosingletons(A,Arity, Term, M, N, LF, L0) :-
	An is A+1,
	arg(An, Term, Arg),
	numbervars_nosingletons(Arg, M, K, LI, L0),
	numbervars_nosingletons(An, Arity, Term, K, N, LF, LI).

%
% if A was left unbound, we have a singleton.
%
number_singletons([]).
number_singletons([-1|L]) :- !,
	number_singletons(L).
number_singletons([_|L]) :-
	number_singletons(L).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% F I N A L  C O M M A N D S

:- aleph_version(V), set(version,V), reset.
