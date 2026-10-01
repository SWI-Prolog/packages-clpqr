/*  $Id$

    Part of CLP(Q) (Constraint Logic Programming over Rationals)

    Author:        Leslie De Koninck
    E-mail:        Leslie.DeKoninck@cs.kuleuven.be
    WWW:           http://www.swi-prolog.org
		   http://www.ai.univie.ac.at/cgi-bin/tr-online?number+95-09
    Copyright (C): 2006, K.U. Leuven and
		   1992-1995, Austrian Research Institute for
		              Artificial Intelligence (OFAI),
			      Vienna, Austria
			
    This software is based on CLP(Q,R) by Christian Holzbaur for SICStus
    Prolog and distributed under the license details below with permission from
    all mentioned authors.

    This program is free software; you can redistribute it and/or
    modify it under the terms of the GNU General Public License
    as published by the Free Software Foundation; either version 2
    of the License, or (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU Lesser General Public
    License along with this library; if not, write to the Free Software
    Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301  USA

    As a special exception, if you link this library with other files,
    compiled with a Free Software compiler, to produce an executable, this
    library does not by itself cause the resulting executable to be covered
    by the GNU General Public License. This exception does not however
    invalidate any other reasons why the executable file might be covered by
    the GNU General Public License.
*/


:- module(fourmotz_q,
	[
	    fm_elim/3
	]).
:- use_module(bv_q,
	[
	    allvars/2,
	    basis_add/2,
	    detach_bounds/1,
	    pivot/5,	
	    var_with_def_intern/4
	]).
:- use_module(library(lists), [reverse/2]).
:- use_module(library(ordsets), [ord_memberchk/2]).
:- use_module('../clpqr/class',
	[
	    class_allvars/2
	]).
:- use_module('../clpqr/project',
	[
	    drop_dep/1,
	    drop_dep_one/1,
	    make_target_indep/2
	]).
:- use_module('../clpqr/redund',
	[
	    redundancy_vars/1
	]).
:- use_module(store_q,
	[
	    add_linear_11/3,
	    add_linear_f1/4,
	    indep/2,
	    normalize_scalar/2
	]).
		


fm_elim(Vs,Target,Pivots) :-
	prefilter(Vs,Vsf),
	fm_elim_int(Vsf,Target,Pivots).

% prefilter(Vars,Res)
%
% filters out target variables and variables that do not occur in bounded linear equations.
% Stores that the variables in Res are to be kept independent.
%
% Which variables occur in a bounded equation is found in one walk over
% each class involved, collecting the order variables of the bounded
% equations, rather than in one walk per variable.

prefilter(Vs,Res) :-
	var_classes(Vs,[],Classes),
	bounded_ords(Classes,Ords0,[]),
	sort(Ords0,Ords),
	prefilter(Vs,Ords,Res).

prefilter([],_,[]).
prefilter([V|Vs],Ords,Res) :-
	(   get_attr(V,clpqr_itf,Att),
	    arg(9,Att,n),
	    arg(5,Att,order(OrdV)),
	    ord_memberchk(OrdV,Ords)
	->  % V is a nontarget variable that occurs in a bounded linear equation
	    Res = [V|Tail],
	    setarg(10,Att,keep_indep),
	    prefilter(Vs,Ords,Tail)
	;   prefilter(Vs,Ords,Res)
	).

var_classes([],Classes,Classes).
var_classes([V|Vs],Classes0,Classes) :-
	(   get_attr(V,clpqr_itf,Att),
	    arg(6,Att,class(C)),
	    \+ memberchk_eq(C,Classes0)
	->  var_classes(Vs,[C|Classes0],Classes)
	;   var_classes(Vs,Classes0,Classes)
	).

% bounded_ords(Classes,Ords,Tail)
%
% Ords are the order variables of the variables occurring in the linear
% equation of a dependent variable with a bound =\= t_none, in Classes.

bounded_ords([],Ords,Ords).
bounded_ords([C|Cs],Ords0,Ords) :-
	class_allvars(C,All),
	bounded_ords_vars(All,Ords0,Ords1),
	bounded_ords(Cs,Ords1,Ords).

bounded_ords_vars(De,Ords,Ords) :-
	var(De),
	!.
bounded_ords_vars([D|De],Ords0,Ords) :-
	(   get_attr(D,clpqr_itf,Att),
	    arg(2,Att,type(Type)),
	    occ_type_filter(Type),
	    arg(4,Att,lin([_,_|Hom]))
	->  hom_ords(Hom,Ords0,Ords1)
	;   Ords1 = Ords0
	),
	bounded_ords_vars(De,Ords1,Ords).

hom_ords([],Ords,Ords).
hom_ords([l(_,Ord)|Ts],[Ord|Ords0],Ords) :-
	hom_ords(Ts,Ords0,Ords).

%
% the target variables are marked with an attribute, and we get a list
% of them as an argument too
%
fm_elim_int([],_,Pivots) :-	% done
	unkeep(Pivots).
fm_elim_int(Vs,Target,Pivots) :-
	Vs = [_|_],
	(   best(Vs,Best,Occ,Rest)
	->  elim_min(Best,Occ,Target,Pivots,NewPivots)
	;   % give up
	    NewPivots = Pivots,
	    Rest = []
	),
	fm_elim_int(Rest,Target,NewPivots).

% best(Vs,Best,Occ,Rest)
%
% Finds the variable with the best result (lowest Delta) and returns its
% occurrences in Occ, as occurences/2 gives them, and the other variables
% in Rest.  Delta is the number of inequalities that
% eliminating the variable adds: those it generates minus those it
% removes.  Candidates are the independent non-target variables in Vs;
% target variables and variables that only occur in unbounded equations
% should have been removed from Vs by prefilter/2.  On equal Delta the
% candidate that comes first in Vs wins.
%
% The occurrences of all candidates are collected in one walk over each
% class, rather than one walk per candidate (occurences/2), which made
% choosing a variable quadratic in the size of the class.

best(Vs,Best,Occ,Rest) :-
	candidates(Vs,1,Cands,[],Classes),
	cand_pairs(Cands,Pairs0),
	keysort(Pairs0,Pairs),	% on the order variable, as linear forms are
	occurrences_in_classes(Classes,Pairs),
	cand_deltas(Cands,Deltas),
	keysort(Deltas,[_-N|_]),
	memberchk(c(N,_,occ(Occ0)),Cands),
	reverse(Occ0,Occ),	% collected in reverse class order
	select_nth(Vs,N,Best,Rest).

% candidates(Vs,N,Cands,Classes0,Classes)
%
% Cands is a list of c(N,OrdX,occ(Occ)) for each candidate X in Vs, N
% being its position in Vs, OrdX its order variable and Occ its
% occurrences, still to be collected.  Classes are the classes of the
% candidates, each once.
%
% The order variables are compared, never changed: every linear form is
% kept sorted on them, and an attribute put on one would move it in the
% standard order of terms.

candidates([],_,[],Classes,Classes).
candidates([X|Xs],N,Cands,Classes0,Classes) :-
	N1 is N+1,
	(   get_attr(X,clpqr_itf,Att),
	    arg(4,Att,lin(Lin)),
	    arg(5,Att,order(OrdX)),
	    arg(9,Att,n),	% no target variable
	    indep(Lin,OrdX)	% X is an independent variable
	->  arg(6,Att,class(C)),
	    Cands = [c(N,OrdX,occ([]))|Cands1],
	    (   memberchk_eq(C,Classes0)
	    ->  Classes1 = Classes0
	    ;   Classes1 = [C|Classes0]
	    ),
	    candidates(Xs,N1,Cands1,Classes1,Classes)
	;   candidates(Xs,N1,Cands,Classes0,Classes)
	).

memberchk_eq(X,[Y|Ys]) :-
	(   X == Y
	->  true
	;   memberchk_eq(X,Ys)
	).

cand_pairs([],[]).
cand_pairs([c(_,Ord,Occ)|Cs],[Ord-Occ|Ps]) :-
	cand_pairs(Cs,Ps).

% occurrences_in_classes(Classes,Pairs)
%
% Adds D:K to the occurrences of each candidate in Pairs, an OrdX-occ(Occ)
% list sorted on OrdX, for each dependent variable D with a bound whose
% linear equation holds the candidate with scalar K.  This is what
% occurences/2 finds for one variable.

occurrences_in_classes([],_).
occurrences_in_classes([C|Cs],Pairs) :-
	class_allvars(C,All),
	occurrences_in_vars(All,Pairs),
	occurrences_in_classes(Cs,Pairs).

occurrences_in_vars(De,_) :-
	var(De),
	!.
occurrences_in_vars([D|De],Pairs) :-
	(   get_attr(D,clpqr_itf,Att),
	    arg(2,Att,type(Type)),
	    occ_type_filter(Type),
	    arg(4,Att,lin([_,_|Hom]))
	->  occurrences_in_hom(Hom,Pairs,D)
	;   true
	),
	occurrences_in_vars(De,Pairs).

% Merge two lists sorted on the order variable.

occurrences_in_hom([],_,_) :- !.
occurrences_in_hom(_,[],_) :- !.
occurrences_in_hom([T|Ts],[O-Occ|Ps],D) :-
	T = l(_*K,OT),
	compare(Rel,OT,O),
	(   Rel = (=)
	->  arg(1,Occ,L),
	    setarg(1,Occ,[D:K|L]),
	    occurrences_in_hom(Ts,Ps,D)
	;   Rel = (<)
	->  occurrences_in_hom(Ts,[O-Occ|Ps],D)
	;   occurrences_in_hom([T|Ts],Ps,D)
	).

% cand_deltas(Cands,Deltas)
%
% Deltas is a list of Delta-N for each candidate that occurs in a bounded
% equation.  cp_card/3 counts pairs, so the order of the occurrences
% does not matter.

cand_deltas([],[]).
cand_deltas([c(N,_,occ(Occ))|Cs],Deltas) :-
	(   Occ = [_|_]
	->  cp_card(Occ,0,Lnew),
	    length(Occ,Locc),
	    Delta is Lnew-Locc,
	    Deltas = [Delta-N|Deltas1]
	;   Deltas = Deltas1
	),
	cand_deltas(Cs,Deltas1).

% select_nth(List,N,Nth,Others)
%
% Selects the N th element of List, stores it in Nth and returns the rest of the list in Others.

select_nth(List,N,Nth,Others) :-
	select_nth(List,1,N,Nth,Others).

select_nth([X|Xs],N,N,X,Xs) :- !.
select_nth([Y|Ys],M,N,X,[Y|Xs]) :-
	M1 is M+1,
	select_nth(Ys,M1,N,X,Xs).

%
% fm_detach + reverse_pivot introduce indep t_none, which
% invalidates the invariants
%
%
% Only the new inequalities can be redundant.  Before the step no bound
% is: project_attributes/2 and every earlier step removed those.  The
% step removes the bounds of the occurrences of V and adds inequalities
% that follow from them, so what the other bounds imply can only shrink
% and none of them becomes redundant.  Checking the whole class here
% made every elimination step cost a simplex run per bounded variable.
%
elim_min(V,Occ,Target,Pivots,NewPivots) :-
	crossproduct(Occ,New,[]),
	activate_crossproduct(New,NewVars),
	reverse_pivot(Pivots),
	fm_detach(Occ),
	allvars(V,All),
	redundancy_vars(NewVars),
	make_target_indep(Target,NewPivots),
	drop_dep(All).

%
% restore NF by reverse pivoting
%
reverse_pivot([]).
reverse_pivot([I:D|Ps]) :-
	get_attr(D,clpqr_itf,AttD),
	arg(2,AttD,type(Dt)),
	setarg(11,AttD,n), % no longer
	get_attr(I,clpqr_itf,AttI),
	arg(2,AttI,type(It)),
	arg(5,AttI,order(OrdI)),
	arg(6,AttI,class(ClI)),
	pivot(D,ClI,OrdI,Dt,It),
	reverse_pivot(Ps).

% unkeep(Pivots)
%
%

unkeep([]).
unkeep([_:D|Ps]) :-
	get_attr(D,clpqr_itf,Att),
	setarg(11,Att,n),
	drop_dep_one(D),
	unkeep(Ps).


%
% All we drop are bounds
%
fm_detach( []).
fm_detach([V:_|Vs]) :-
	detach_bounds(V),
	fm_detach(Vs).

% activate_crossproduct(Lst,Vars)
%
% For each inequality Lin =< 0 (or Lin < 0) in Lst, a new variable is created:
% Var = Lin and Var =< 0 (or Var < 0). Var is added to the basis.  Vars
% are the new variables.

activate_crossproduct([],[]).
activate_crossproduct([lez(Strict,Lin)|News],[Var|Vars]) :-
	var_with_def_intern(t_u(0),Var,Lin,Strict),
	% Var belongs to same class as elements in Lin
	basis_add(Var,_),
	activate_crossproduct(News,Vars).

% ------------------------------------------------------------------------------

% crossproduct(Lst,Res,ResTail)
%
% See crossproduct/4
% This predicate each time puts the next element of Lst as First in crossproduct/4
% and lets the rest be Next.

crossproduct([]) --> [].
crossproduct([A|As]) -->
	crossproduct(As,A),
	crossproduct(As).

% crossproduct(Next,First,Res,ResTail)
%
% Eliminates a variable in linear equations First + Next and stores the generated
% inequalities in Res.
% Let's say A:K1 = First and B:K2 = first equation in Next.
% A = ... + K1*V + ...
% B = ... + K2*V + ...
% Let K = -K2/K1
% then K*A + B = ... + 0*V + ...
% from the bounds of A and B, via cross_lower/7 and cross_upper/7, new inequalities
% are generated. Then the same is done for B:K2 = next element in Next.

crossproduct([],_) --> [].
crossproduct([B:Kb|Bs],A:Ka) -->
	{
	    get_attr(A,clpqr_itf,AttA),
	    arg(2,AttA,type(Ta)),
	    arg(3,AttA,strictness(Sa)),
	    arg(4,AttA,lin(LinA)),
	    get_attr(B,clpqr_itf,AttB),
	    arg(2,AttB,type(Tb)),
	    arg(3,AttB,strictness(Sb)),
	    arg(4,AttB,lin(LinB)),
	    K is -Kb rdiv Ka,
	    add_linear_f1(LinA,K,LinB,Lin)	% Lin doesn't contain the target variable anymore
	},
	(   { K > 0 }	% K > 0: signs were opposite
	->  { Strict is Sa \/ Sb },
	    cross_lower(Ta,Tb,K,Lin,Strict),
	    cross_upper(Ta,Tb,K,Lin,Strict)
	;   % La =< A =< Ua -> -Ua =< -A =< -La
    	    {
		flip(Ta,Taf),
		flip_strict(Sa,Saf),
		Strict is Saf \/ Sb
	    },
	    cross_lower(Taf,Tb,K,Lin,Strict),
	    cross_upper(Taf,Tb,K,Lin,Strict)
	),
	crossproduct(Bs,A:Ka).

% cross_lower(Ta,Tb,K,Lin,Strict,Res,ResTail)
%
% Generates a constraint following from the bounds of A and B.
% When A = LinA and B = LinB then Lin = K*LinA + LinB. Ta is the type
% of A and Tb is the type of B. Strict is the union of the strictness
% of A and B. If K is negative, then Ta should have been flipped (flip/2).
% The idea is that if La =< A =< Ua and Lb =< B =< Ub (=< can also be <)
% then if K is positive, K*La + Lb =< K*A + B =< K*Ua + Ub.
% if K is negative, K*Ua + Lb =< K*A + B =< K*La + Ub.
% This predicate handles the first inequality and adds it to Res in the form
% lez(Sl,Lhs) meaning K*La + Lb - (K*A + B) =< 0 or K*Ua + Lb - (K*A + B) =< 0
% with Sl being the strictness and Lhs the lefthandside of the equation.
% See also cross_upper/7

cross_lower(Ta,Tb,K,Lin,Strict) -->
	{
	    lower(Ta,La),
	    lower(Tb,Lb),
	    !,
	    L is K*La+Lb,
	    normalize_scalar(L,Ln),
	    add_linear_f1(Lin,-1,Ln,Lhs),
	    Sl is Strict >> 1			% normalize to upper bound
	},
	[ lez(Sl,Lhs) ].
cross_lower(_,_,_,_,_) --> [].

% cross_upper(Ta,Tb,K,Lin,Strict,Res,ResTail)
%
% See cross_lower/7
% This predicate handles the second inequality:
% -(K*Ua + Ub) + K*A + B =< 0 or -(K*La + Ub) + K*A + B =< 0

cross_upper(Ta,Tb,K,Lin,Strict) -->
	{
	    upper(Ta,Ua),
	    upper(Tb,Ub),
	    !,
	    U is -(K*Ua+Ub),
	    normalize_scalar(U,Un),
	    add_linear_11(Un,Lin,Lhs),
	    Su is Strict /\ 1			% normalize to upper bound
	},
	[ lez(Su,Lhs) ].
cross_upper(_,_,_,_,_) --> [].

% lower(Type,Lowerbound)
%
% Returns the lowerbound of type Type if it has one.
% E.g. if type = t_l(L) then Lowerbound is L,
%      if type = t_lU(L,U) then Lowerbound is L,
%      if type = t_u(U) then fails

lower(t_l(L),L).
lower(t_lu(L,_),L).
lower(t_L(L),L).
lower(t_Lu(L,_),L).
lower(t_lU(L,_),L).

% upper(Type,Upperbound)
%
% Returns the upperbound of type Type if it has one.
% See lower/2

upper(t_u(U),U).
upper(t_lu(_,U),U).
upper(t_U(U),U).
upper(t_Lu(_,U),U).
upper(t_lU(_,U),U).

% flip(Type,FlippedType)
%
% Flips the lower and upperbound, so the old lowerbound becomes the new upperbound and
% vice versa.

flip(t_l(X),t_u(X)).
flip(t_u(X),t_l(X)).
flip(t_lu(X,Y),t_lu(Y,X)).
flip(t_L(X),t_u(X)).
flip(t_U(X),t_l(X)).
flip(t_lU(X,Y),t_lu(Y,X)).
flip(t_Lu(X,Y),t_lu(Y,X)).

% flip_strict(Strict,FlippedStrict)
%
% Does what flip/2 does, but for the strictness.

flip_strict(0,0).
flip_strict(1,2).
flip_strict(2,1).
flip_strict(3,3).

% cp_card(Lst,CountIn,CountOut)
%
% Counts the number of bounds that may generate an inequality in
% crossproduct/3

cp_card([],Ci,Ci).
cp_card([A|As],Ci,Co) :-
	cp_card(As,A,Ci,Cii),
	cp_card(As,Cii,Co).

% cp_card(Next,First,CountIn,CountOut)
%
% Counts the number of bounds that may generate an inequality in
% crossproduct/4.

cp_card([],_,Ci,Ci).
cp_card([B:Kb|Bs],A:Ka,Ci,Co) :-
	get_attr(A,clpqr_itf,AttA),
	arg(2,AttA,type(Ta)),
	get_attr(B,clpqr_itf,AttB),
	arg(2,AttB,type(Tb)),
	(   sign(Ka) =\= sign(Kb)
	->  cp_card_lower(Ta,Tb,Ci,Cii),
	    cp_card_upper(Ta,Tb,Cii,Ciii)
	;   flip(Ta,Taf),
	    cp_card_lower(Taf,Tb,Ci,Cii),
	    cp_card_upper(Taf,Tb,Cii,Ciii)
	),
	cp_card(Bs,A:Ka,Ciii,Co).

% cp_card_lower(TypeA,TypeB,SIn,SOut)
%
% SOut = SIn + 1 if both TypeA and TypeB have a lowerbound.

cp_card_lower(Ta,Tb,Si,So) :-
	lower(Ta,_),
	lower(Tb,_),
	!,
	So is Si+1.
cp_card_lower(_,_,Si,Si).

% cp_card_upper(TypeA,TypeB,SIn,SOut)
%
% SOut = SIn + 1 if both TypeA and TypeB have an upperbound.

cp_card_upper(Ta,Tb,Si,So) :-
	upper(Ta,_),
	upper(Tb,_),
	!,
	So is Si+1.
cp_card_upper(_,_,Si,Si).

% ------------------------------------------------------------------------------

% occ_type_filter(Type)
%
% Succeeds when Type is any other type than t_none. Is used in occurences/3 and occurs/2

occ_type_filter(t_l(_)).
occ_type_filter(t_u(_)).
occ_type_filter(t_lu(_,_)).
occ_type_filter(t_L(_)).
occ_type_filter(t_U(_)).
occ_type_filter(t_lU(_,_)).
occ_type_filter(t_Lu(_,_)).
