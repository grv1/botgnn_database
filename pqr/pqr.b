:- set(clauselength,7).

:- mode(*, p(+any)).
:- mode(*, q(+any,-any)).
:- mode(*, r1(+any)).
:- mode(*, r2(+any)).
:- mode(*, r3(+any)).
:- mode(*, r4(+any)).

:- determination(p/1, q/2).
:- determination(p/1, r1/1).
:- determination(p/1, r2/1).
:- determination(p/1, r3/1).
:- determination(p/1, r4/1).

q(x,y).
q(x,z).
q(a,b).
q(a,c).
r1(y).
r1(b).
r2(y).
r2(c).
r3(z).
r3(b).
r4(z).
r4(c).

q(u,v).
q(u,w).
r1(v).
r2(v).
r3(w).
r4(w).