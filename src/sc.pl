:- op(1150,xfy,or). % Disjunction
:- op(1150,fx,neg). % Negation
:- op(1150,xfy,and). % Conjuction
:- op(1150,xfy,impl). % Implication
:- op(1150,xfy,iff). % Double Implication

dnf(A,A) :- atom(A).
dnf(neg A,neg C) :- dnf(A,C).
dnf(A or B,C or D) :- dnf(A,C),dnf(B,D).
dnf(A and B,neg((neg C) or (neg D))) :- dnf(A,C),dnf(B,D).
dnf(A impl B,(neg C) or D) :- dnf(A,C),dnf(B,D).
dnf(A iff B,C) :- dnf((A impl B) and (B impl A),C).

dnfL([],[]).
dnfL([F|Fs],[G|Gs]) :- dnf(F,G),dnfL(Fs,Gs).

sc(I,D) :- not(intersection(I,D,[])).
sc([(neg F)|I],D) :- sc_aux(I,[F|D]).
sc(I,[(neg F)|D]) :- sc_aux([F|I],D).
sc(I,[(F1 or F2)|D]) :- union([F1,F2],D,D1),sc_aux(I,D1).
sc([(F1 or F2)|I],D) :- sc_aux([F1|I],D),sc_aux([F2|I],D).

sc_aux(I,D):-permutation(I,I1),permutation(D,D1),sc(I1,D1).

sc1(I,D) :- dnfL(I,I1),dnfL(D,D1),sc(I1,D1).
