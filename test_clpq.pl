/*  Part of CLP(Q,R) (Constraint Logic Programming over Rationals and Reals)

    Author:        Jan Wielemaker
    E-mail:        jan@swi-prolog.org
    WWW:           http://www.swi-prolog.org
    Copyright (c)  2026, SWI-Prolog Solutions b.v.
    All rights reserved.

    Redistribution and use in source and binary forms, with or without
    modification, are permitted provided that the following conditions
    are met:

    1. Redistributions of source code must retain the above copyright
       notice, this list of conditions and the following disclaimer.

    2. Redistributions in binary form must reproduce the above copyright
       notice, this list of conditions and the following disclaimer in
       the documentation and/or other materials provided with the
       distribution.

    THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
    "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
    LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS
    FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE
    COPYRIGHT OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT,
    INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING,
    BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
    LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
    CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
    LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN
    ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
    POSSIBILITY OF SUCH DAMAGE.
*/

:- module(test_clpq,
          [ test_clpq/0
          ]).
:- use_module(library(plunit)).
:- use_module(library(lists)).
:- use_module(library(ordsets)).
:- use_module(library(clpq)).
:- use_module(library(clpr), []).          % for the solver-mixing tests

/** <module> Test CLP(Q)

Tests for library(clpq).  The structure follows doc/design.md.  Tests in
the unit `clpq_known_issues` pin down behaviour that is *wrong*; they are
there to make sure a fix is noticed, and each carries a comment saying
what the answer should be.

@see doc/design.md
*/

test_clpq :-
    run_tests([ clpq_syntax,
                clpq_nf,
                clpq_equations,
                clpq_inequalities,
                clpq_disequations,
                clpq_nonlinear,
                clpq_entailment,
                clpq_optimisation,
                clpq_bb,
                clpq_projection,
                clpq_projection_random,
                clpq_residuals,
                clpq_unify,
                clpq_examples,
                clpq_toplevel,
                clpq_internals,
                clpq_known_issues
              ]).

%!  det_call(:Goal, -Det) is semidet.
%
%   As call/1, but Det is `true` when Goal left no choice point.  This
%   is how plunit itself detects nondeterminism; using it in a test turns
%   what plunit would only warn about into a failure.

:- meta_predicate det_call(0, -).

det_call(Goal, Det) :-
    call_cleanup(Goal, Det0 = true),
    (   var(Det0)
    ->  Det = false
    ;   Det = true
    ).

%!  geler_goals(+Var, -Live, -Spent) is det.
%
%   Count the delayed non-linear goals attached to Var and how many of
%   them have already run.  A goal that has run must not stay attached.

geler_goals(V, Live, Spent) :-
    (   get_attr(V, clpqr_geler, g(_,goals(G),_))
    ->  count_goals(G, 0-0, Live-Spent)
    ;   Live = 0,
        Spent = 0
    ).

count_goals((A,B), S0, S) :-
    !,
    count_goals(A, S0, S1),
    count_goals(B, S1, S).
count_goals(run(M,_), L0-S0, L-S) :-
    !,
    L is L0+1,
    (   nonvar(M)
    ->  S is S0+1
    ;   S = S0
    ).
count_goals(_, S, S).

		 /*******************************
		 *           SYNTAX		*
		 *******************************/

:- begin_tests(clpq_syntax).

test(conjunction, X == 2) :-
    {X > 1, X < 3, X =:= 2}.
test(nested_conjunction, [X == 1, Y == 2]) :-
    {(X =:= 1, Y =:= 2)}.
test(disjunction, all(X == [1,2])) :-
    {X =:= 1 ; X =:= 2}.
test(less) :-
    {X < 3, X > 2, X =:= 5r2}.
test(greater) :-
    {3 > X, 2 < X, X =:= 5r2}.
test(leq, X == 3) :-
    {X =< 3, X >= 3}.
test(leq_alt, X == 3) :-
    {<=(X, 3)}, {X >= 3}.
test(eq_is, X == 3) :-
    {X =:= 3}.
test(eq_unify, X == 3) :-
    {X = 3}.
test(unary_minus, X == 3) :-
    {X =:= -(-3)}.
test(unary_plus, X == 3) :-
    {X =:= +3}.
test(division_exact, X == 1r3) :-
    {X =:= 1/3}.
test(float_is_rationalized, X == 3r2) :-
    {X =:= 1.5}.
test(abs, X == 7) :-
    {X =:= abs(-7)}.
test(min, X == 3) :-
    {X =:= min(3,4)}.
test(max, X == 4) :-
    {X =:= max(3,4)}.
test(pow, X == 1024) :-
    {X =:= pow(2,10)}.
test(hat, X == 1024) :-
    {X =:= 2^10}.
test(exp2, X == 1024) :-
    {X =:= exp(2,10)}.
test(negative_power, X == 1r4) :-
    {X =:= 2^(-2)}.
test(zero_power, X == 1) :-
    {X =:= 5^0}.

% Errors

test(var_constraint, error(instantiation_error)) :-
    {_}.
test(bad_constraint, error(type_error(clpq_constraint, foo))) :-
    {foo}.
test(bad_expression, error(type_error(clpq_expression, a))) :-
    {_ =:= a}.
test(star_star_rejected, error(type_error(clpq_expression, 2**3))) :-
    {_ =:= 2**3}.
test(sqrt_rejected, error(type_error(clpq_expression, sqrt(4)))) :-
    {_ =:= sqrt(4)}.
test(rdiv_rejected, error(type_error(clpq_expression, 1 rdiv 2))) :-
    X = 1 rdiv 2,
    {_ =:= X}.
test(entailed_var, error(instantiation_error)) :-
    entailed(_).
test(entailed_bad, error(type_error(clpq_constraint, foo))) :-
    entailed(foo).
test(bb_inf_bad_int, error(type_error(var, _))) :-
    {X >= 0},
    bb_inf([_+_], X, _).

:- end_tests(clpq_syntax).

		 /*******************************
		 *        NORMAL FORM		*
		 *******************************/

:- begin_tests(clpq_nf).

test(cancel) :-
    {X - X =:= 0}, var(X).
test(cancel_sum, Y == 1) :-
    {Y =:= X + 1 - X}.
test(collect, Y == 0) :-
    {Y =:= 2*X + 3*X - 5*X}.
test(distribute, Y == -1) :-
    {Y =:= (X+1)*(X-1) - X*X}.
test(binomial, Y == 1) :-
    {Y =:= (X+1)^2 - X^2 - 2*X}.
test(binomial_big, Y == 0) :-
    {Y =:= (1+X)^3 - (1 + 3*X + 3*X^2 + X^3)}.
test(scalar_product, X == 12) :-
    {X =:= 3*4}.
test(division_by_variable_is_nonlinear, true(var(X))) :-
    {_ =:= 1/X}.
test(division_by_zero_fails, fail) :-
    {_ =:= 1/0}.
test(mult_two_vars_is_nonlinear, true((var(X),var(Y),var(Z)))) :-
    {Z =:= X*Y}.
test(mult_by_constant_is_linear, Z == 6) :-
    {Z =:= 3*X, X =:= 2}.

:- end_tests(clpq_nf).

		 /*******************************
		 *          EQUATIONS		*
		 *******************************/

:- begin_tests(clpq_equations).

test(two_by_two, [X == 2, Y == 1]) :-
    {2*X + 3*Y =:= 7, X - Y =:= 1}.
test(three_by_three, [X == 1, Y == 2, Z == 3]) :-
    { X + Y + Z =:= 6,
      X - Y + Z =:= 2,
      X + Y - Z =:= 0 }.
test(rational_solution, X == 1r3) :-
    {3*X =:= 1}.
test(inconsistent, fail) :-
    {X + Y =:= 1, X + Y =:= 2}.
test(dependent_rows, true((var(X),var(Y)))) :-
    {X + Y =:= 1, 2*X + 2*Y =:= 2}.
test(implied_value, [X == 2, Y == 1]) :-
    % A rank-2 system over two variables implies both values
    {X + Y =:= 3},
    assertion((var(X),var(Y))),
    {X - Y =:= 1}.
test(class_merge, [Y == 1, Z == 1, W == 1]) :-
    {X + Y =:= 1},
    {Z + W =:= 2},
    {Y =:= Z},
    {X =:= 0}.
test(alias, Y == 1) :-
    {X =:= Y}, {X =:= 1}.
test(chain, A == 7) :-
    {A =:= B, B =:= C, C =:= D, D =:= 7}.
test(negative_coefficients, [X == 2, Y == 1]) :-
    {-X - Y =:= -3, X - Y =:= 1}.
test(large_system, true(integer(First))) :-
    numlist(1, 30, Ns),
    length(Vs, 30),
    make_chain(Vs, Ns),
    last(Vs, Last),
    {Last =:= 0},
    nth1(1, Vs, First).

% V1-V2 =:= N1, V2-V3 =:= N2, ...
make_chain([_], [_]) :- !.
make_chain([A,B|T], [N|Ns]) :-
    {A - B =:= N},
    make_chain([B|T], Ns).

:- end_tests(clpq_equations).

		 /*******************************
		 *        INEQUALITIES		*
		 *******************************/

:- begin_tests(clpq_inequalities).

test(simple_bounds, [I == 1, S == 3]) :-
    {X >= 1, X =< 3},
    assertion(var(X)),
    inf(X, I), sup(X, S).
test(meeting_bounds, X == 2) :-
    {X >= 2, X =< 2}.
test(strict_meeting_bounds, fail) :-
    {X > 2, X =< 2}.
test(strict_both, fail) :-
    {X > 2, X < 2}.
test(empty_interval, fail) :-
    {X >= 3, X =< 2}.
test(tighten_lower, [true(\+ entailed(X >= 3)), true(entailed(X >= 2))]) :-
    {X >= 1}, {X >= 2}, {X >= 0}.
test(tighten_upper, [true(entailed(X =< 3)), true(\+ entailed(X =< 2))]) :-
    {X =< 5}, {X =< 3}, {X =< 9}.
test(strictness_kept, [true(\+ {X =:= 1}), true(entailed(X >= 1))]) :-
    {X > 1}.
test(strictness_upgrade, true(\+ {X =:= 1})) :-
    {X >= 1}, {X > 1}.
test(no_strictness_downgrade, true(\+ {X =:= 1})) :-
    {X > 1}, {X >= 1}.
test(two_variables, S == 10) :-
    {X + Y =< 10, X >= 0, Y >= 0},
    sup(X, S).
test(triangle, Y == 0) :-
    {X >= 0, Y >= 0, X + Y =< 1},
    assertion(\+ {X =:= 1, Y =:= 1}),
    {X =:= 1}.
test(unbounded_sup, fail) :-
    {X >= 0},
    sup(X, _).
test(unbounded_inf, fail) :-
    {X =< 0},
    inf(X, _).
test(transitive, [Y == 1, Z == 1]) :-
    {X =< Y, Y =< Z, Z =< X},
    {X =:= 1}.
test(transitive_strict, fail) :-
    {X < Y, Y < Z, Z < X}.
test(slack_elimination, [A == 1, B == 1, C == 1, D == 1]) :-
    % 12 constraints over 4 variables, all implying a single point
    { A >= 0, B >= 0, C >= 0, D >= 0,
      A + B + C + D =< 4,
      A + B + C + D >= 4,
      A =< 1, B =< 1, C =< 1, D =< 1 }.
test(negative_bounds, S == -5) :-
    {X =< -5},
    assertion(entailed(X < 0)),
    sup(X, S).
test(scaled_bound, S == 7r3) :-
    {3*X =< 7},
    sup(X, S).
test(mixed_eq_ineq, [I == 0, S == 10]) :-
    {X + Y =:= 10, X >= 0, Y >= 0},
    inf(X, I), sup(X, S).

:- end_tests(clpq_inequalities).

		 /*******************************
		 *        DISEQUATIONS		*
		 *******************************/

:- begin_tests(clpq_disequations).

test(ground_true) :-
    {1 =\= 2}.
test(ground_false, fail) :-
    {1 =\= 1}.
test(delayed_ok, X == 4) :-
    {X =\= 3},
    {X =:= 4}.
test(delayed_violated, fail) :-
    {X =\= 3},
    {X =:= 3}.
test(delayed_violated_unify, fail) :-
    {X =\= 3},
    X = 3.
test(two_variables) :-
    {X =\= Y},
    {X =:= 1},
    assertion(\+ {Y =:= 1}),
    {Y =:= 2}.
test(expression, true(\+ {Y =:= 1})) :-
    {X + Y =\= 1},
    {X =:= 0}.
test(alldifferent) :-
    {A =\= B, B =\= C, A =\= C},
    {A =:= 1, B =:= 2, C =:= 3}.
test(alldifferent_violated, fail) :-
    {A =\= B, B =\= C, A =\= C},
    {A =:= 1, B =:= 2, C =:= 1}.
test(residual_shape, C == [x =\= 3]) :-
    {X =\= 3},
    dump([X], [x], C).

:- end_tests(clpq_disequations).

		 /*******************************
		 *         NON-LINEAR		*
		 *******************************/

:- begin_tests(clpq_nonlinear).

test(spent_goals_are_not_retained, [Live == 4, Spent == 0]) :-
    % unifying two variables that both carry delayed goals runs those
    % goals; they must not stay attached to the survivor.  geler.pl said
    % del_attr(Y,geler) where the attribute is named clpqr_geler, so the
    % spent goals were never dropped and the conjunction grew as N^2.
    {A*_ =:= 1}, {B*_ =:= 2}, {C*_ =:= 3}, {D*_ =:= 4},
    A = B, A = C, A = D,
    geler_goals(A, Live, Spent).
test(waking_is_deterministic, [Det == true, Y == 3]) :-
    % waking a delayed goal used to leave a choice point behind, in
    % geler.pl's run/2 and attr_unify_hook/2 and in nf_q.pl's repair_p/5
    {X*Y =:= 6},
    det_call({X =:= 2}, Det).
test(delayed_product, [Y == 3]) :-
    {X*Y =:= 6},
    assertion((var(X), var(Y))),
    {X =:= 2}.
test(delayed_product_other_way, [X == 2]) :-
    {X*Y =:= 6},
    {Y =:= 3}.
test(square_root, all(X == [2,-2])) :-
    % the isolating axiom for X = Y^Z: an even power has two roots
    {X*X =:= 4}.
test(square_root_irrational, fail) :-
    % sqrt(2) is not rational, so over Q this has no solution at all
    {X*X =:= 2}.
test(square_checked_on_binding, [nondet]) :-
    {X*X =:= 4}, {X =:= 2}.
test(square_violation_detected, fail) :-
    {X*X =:= 4}, {X =:= 3}.
test(cube_root, X == 2) :-
    {8 =:= X^3}.
test(cube_root_negative, X == -2) :-
    {-8 =:= X^3}.
test(rational_root, X == 1r2) :-
    {1r8 =:= X^3}.
test(negative_exponent_root, all(X == [1r2,-1r2])) :-
    {4 =:= X^(-2)}.
test(tenth_root, all(X == [2,-2])) :-
    {1024 =:= X^10}.
test(even_root_of_negative, fail) :-
    {-4 =:= _X^2}.
test(zero_root, X == 0) :-
    {0 =:= X^2}.
test(reciprocal_is_never_zero, fail) :-
    {0 =:= 1/_X}.
test(root_after_waking, all(X == [2,-2])) :-
    % the power is resolved when the right hand side becomes known
    {X^2 =:= Y}, {Y =:= 4}.
test(division_delayed, [X == 6]) :-
    {X/Y =:= 2},
    {Y =:= 3}.
test(abs_delayed, [X == 4]) :-
    {X =:= abs(Y)},
    {Y =:= -4}.
test(min_delayed, [X == 1]) :-
    {X =:= min(Y,3)},
    {Y =:= 1}.
test(max_delayed, [X == 5]) :-
    {X =:= max(Y,3)},
    {Y =:= 5}.
test(invert_sin, X == 0) :-
    {0 =:= sin(X)}.
test(invert_cos, X == 0) :-
    {1 =:= cos(X)}.
test(invert_tan, X == 0) :-
    {0 =:= tan(X)}.
test(invert_exp_base, Y == 3) :-
    {8 =:= 2^Y}.
test(invert_exp_base_rounding, Y == 3) :-
    % log(1000)/log(10) is 2.9999999999999996 in floating point
    {1000 =:= 10^Y}.
test(invert_exp_base_large, Y == 10) :-
    {59049 =:= 3^Y}.
test(invert_exp_base_negative, Y == -3) :-
    {1r8 =:= 2^Y}.
test(invert_exp_base_fractional, Y == 1r3) :-
    {2 =:= 8^Y}.
test(invert_exp_base_unity, Y == 0) :-
    {1 =:= 2^Y}.
test(invert_exp_base_irrational,
     [ true(rational(Y))
     , true(abs(Y - 1.584962500721156) < 1r1000000000000000)
     ]) :-
    % log2(3) is irrational: the best we can do is the simplest rational
    % that maps back to the same float
    {3 =:= 2^Y}.
test(invert_exp_exponent,
     [ true(rational(Y))
     , true(abs(Y - 2.2973967099940698) < 1r1000000000000000)
     ]) :-
    % the other branch of nl_invertible/4: X and Z ground in X = Y^Z
    {8 =:= Y^2.5}.
test(nonlinear_becomes_linear, [Z == 1]) :-
    {Z =:= X*_Y + 1},
    {X =:= 0}.
test(goal_runs_once) :-
    % X and Y in one delayed goal; binding both must not run it twice
    {X*Y =:= 6},
    {X =:= 2, Y =:= 3}.
test(delayed_inequality, [true(entailed(Y =< 3))]) :-
    {X*Y =< 6},
    {X =:= 2}.
test(delayed_inequality_violated, fail) :-
    {X*Y =< 6},
    {X =:= 2, Y =:= 4}.
test(delayed_disequation, fail) :-
    {X*Y =\= 6},
    {X =:= 2, Y =:= 3}.
test(power_of_variable_delayed, [Y == 8]) :-
    {Y =:= X^3},
    {X =:= 2}.

:- end_tests(clpq_nonlinear).

		 /*******************************
		 *         ENTAILMENT		*
		 *******************************/

:- begin_tests(clpq_entailment).

test(trivial) :-
    entailed(1 =:= 1).
test(trivial_false, fail) :-
    entailed(1 =:= 2).
test(from_equality) :-
    {X =:= 3},
    entailed(X > 2),
    entailed(X >= 3),
    entailed(X =\= 4).
test(from_bounds) :-
    {X >= 1, X =< 2},
    entailed(X > 0),
    entailed(X < 3),
    \+ entailed(X > 1),
    \+ entailed(X =:= 1).
test(strict_bound) :-
    {X > 1},
    entailed(X >= 1),
    \+ entailed(X > 1 + 1r1000000).
test(conjunction) :-
    {X >= 1, X =< 2},
    entailed((X >= 1, X =< 2)).
test(disjunction) :-
    {X >= 1, X =< 2},
    entailed((X =< 0 ; X >= 1)).
test(linear_combination) :-
    {X + Y =:= 10, X >= 0, Y >= 0},
    entailed(X =< 10),
    entailed(X + Y >= 10).
test(does_not_change_store, Before == After) :-
    {X >= 1, X =< 2},
    dump([X], [x], Before),
    ( entailed(X > 5) -> true ; true ),
    dump([X], [x], After).

:- end_tests(clpq_entailment).

		 /*******************************
		 *        OPTIMISATION		*
		 *******************************/

:- begin_tests(clpq_optimisation).

test(inf_simple, I == 1) :-
    {X >= 1, X =< 5},
    inf(X, I).
test(sup_simple, S == 5) :-
    {X >= 1, X =< 5},
    sup(X, S).
test(inf_does_not_bind, S == 5) :-
    {X >= 1, X =< 5},
    inf(X, _),
    assertion(var(X)),
    sup(X, S).
test(inf_expression, I == 2) :-
    {X >= 1, Y >= 1, X + Y =< 4},
    inf(X + Y, I).
test(sup_expression, S == 4) :-
    {X >= 1, Y >= 1, X + Y =< 4},
    sup(X + Y, S).
test(inf_rational, I == 1r3) :-
    {3*X >= 1},
    inf(X, I).
test(inf_vertex, [I == 2, V == [1,1]]) :-
    {X >= 1, Y >= 1, X + Y =< 4},
    inf(X + Y, I, [X,Y], V).
test(sup_vertex, [S == 4, true(sum_of(V, 4))]) :-
    {X >= 1, Y >= 1, X + Y =< 4},
    sup(X + Y, S, [X,Y], V).
test(minimize, X == 2) :-
    {X >= 2, X =< 7},
    minimize(X).
test(maximize, X == 7) :-
    {X >= 2, X =< 7},
    maximize(X).
test(minimize_expression, [X == 1, Y == 1]) :-
    {X >= 1, Y >= 1, X + Y =< 4},
    minimize(X + Y).
test(maximize_expression, true(entailed(X + Y =:= 4))) :-
    {X >= 1, Y >= 1, X + Y =< 4},
    maximize(X + Y).
test(lp_diet, I == 34r5) :-
    % Minimise 2*A + 3*B subject to a couple of covering constraints
    { A >= 0, B >= 0,
      A + 2*B >= 4,
      3*A + B >= 6 },
    inf(2*A + 3*B, I).
test(unbounded_inf_fails, fail) :-
    {X >= 0},
    inf(-X, _).
test(strict_bound_infimum, I == 1) :-
    % The infimum of a strictly bounded expression is the open bound
    {X > 1, X =< 5},
    inf(X, I).
% the optimum used to be carried across in the global variable `inf'
test(does_not_touch_global_variables, [I == 1, S == 5, V == mine]) :-
    nb_setval(inf, mine),
    {X >= 1, X =< 5},
    inf(X, I),
    sup(X, S),
    nb_getval(inf, V),
    nb_delete(inf).
test(inf_waits_for_linear, [I == 3]) :-
    {X*Y >= 3},
    {X =:= 1},
    inf(Y, I).

sum_of(L, S) :-
    foldl([X,A0,A]>>(A is A0+X), L, 0, S).

:- end_tests(clpq_optimisation).

		 /*******************************
		 *      BRANCH AND BOUND	*
		 *******************************/

:- begin_tests(clpq_bb).

test(single_variable, I == 1) :-
    {X >= 1r2, X =< 7r2},
    bb_inf([X], X, I).
test(single_variable_vertex, [I == 1, V == [1]]) :-
    {X >= 1r2, X =< 7r2},
    bb_inf([X], X, I, V).
test(two_variables, I == 1) :-
    {X >= 0, Y >= 0, X + Y >= 1},
    bb_inf([X,Y], X + Y, I).
test(fractional_optimum, I == 1) :-
    % LP optimum is 1/2, MIP optimum is 1
    {2*X >= 1, X >= 0},
    bb_inf([X], X, I).
test(does_not_bind, LpInf == 1r2) :-
    {X >= 1r2, X =< 7r2},
    bb_inf([X], X, _),
    assertion(var(X)),
    inf(X, LpInf).
test(strict_bound, I == 2) :-
    {X > 1, X =< 5},
    bb_inf([X], X, I).
test(knapsack, I == 3) :-
    { A >= 0, B >= 0,
      A =< 3, B =< 3,
      2*A + 3*B >= 7 },
    bb_inf([A,B], A + B, I).
test(objective_not_integral, I == 5r4) :-
    % Only X is required to be integral
    {X >= 1r2, Y >= 1r4},
    bb_inf([X], X + Y, I).
test(ground_integer_ok, I == 0) :-
    {X >= 0},
    bb_inf([2], X, I).
test(ground_noninteger_fails, fail) :-
    {X >= 0},
    bb_inf([3r2], X, _).
test(unbounded_fails, fail) :-
    {X >= 0},
    bb_inf([X], -X, _).
% the incumbent used to live in the global variable `prov_opt'
test(does_not_touch_global_variables, [I == 1, V == mine]) :-
    nb_setval(prov_opt, mine),
    {X >= 1r2, X =< 7r2},
    bb_inf([X], X, I),
    nb_getval(prov_opt, V),
    nb_delete(prov_opt).
test(nested_calls_do_not_interfere, [I1 == 1, I2 == 3, I3 == 1]) :-
    {X >= 1r2, X =< 7r2},
    {Y >= 5r2, Y =< 9r2},
    bb_inf([X], X, I1),
    bb_inf([Y], Y, I2),
    bb_inf([X], X, I3).

test(ground_objective, I == 3) :-
    % bb_reoptimize/2's second clause: the objective is already determined,
    % so there is nothing left to optimise
    {X =:= 3},
    bb_inf([X], X, I).
test(ground_objective_expression, I == 1) :-
    {X >= 1, X =< 1},
    bb_inf([X], X+0, I).

:- end_tests(clpq_bb).

		 /*******************************
		 *         PROJECTION		*
		 *******************************/

:- begin_tests(clpq_projection).

test(empty, C == []) :-
    dump([], [], C).
test(unconstrained, C == []) :-
    dump([_], [x], C).
test(equation, C == [y = 1-x]) :-
    {X + Y =:= 1},
    dump([X,Y], [x,y], C).
test(bounds, C == [x >= 1, x =< 3]) :-
    {X >= 1, X =< 3},
    dump([X], [x], C).
test(strict_bounds, C == [x > 1, x < 3]) :-
    {X > 1, X < 3},
    dump([X], [x], C).
test(scaled, C == [x >= 1r2]) :-
    {2*X >= 1},
    dump([X], [x], C).
test(redundant_bounds_removed, C == [x >= 2]) :-
    {X >= 1, X >= 2, X >= 0},
    dump([X], [x], C).
test(projection_eliminates_variable, C == []) :-
    % Y only has a lower bound, so X is unconstrained after projection
    {X + Y >= 1, Y >= 0},
    dump([X], [x], C).
test(fourier_motzkin, C == [x-z =< 0]) :-
    % X =< Y =< Z implies X =< Z
    {X =< Y, Y =< Z},
    dump([X,Z], [x,z], C).
test(does_not_change_store, [I == 1, S == 3]) :-
    {X >= 1, X =< 3},
    dump([X], [x], _),
    inf(X, I), sup(X, S).
test(nonlinear_residue, true(C = [_])) :-
    {X*Y =:= 6},
    dump([X,Y], [x,y], C).
test(target_order_does_not_control_shape, C1 == C2) :-
    % dump/3 only interns its targets; it does not impose an ordering of
    % its own, so an explicit ordering/1 is never contradicted
    {X + Y =:= 1},
    dump([X,Y], [x,y], C1),
    dump([Y,X], [y,x], C2).
test(ordering_list_controls_shape, C == [y = 1-x]) :-
    % the variable that comes first is the one the answer defines
    {X + Y =:= 1},
    ordering([Y,X]),
    dump([X,Y], [x,y], C).
test(ordering_list_controls_shape_2, C == [x = 1-y]) :-
    {X + Y =:= 1},
    ordering([X,Y]),
    dump([X,Y], [x,y], C).
test(ordering_lt_controls_shape, C == [y = 1-x]) :-
    {X + Y =:= 1},
    ordering(Y < X),
    dump([X,Y], [x,y], C).
test(ordering_gt_controls_shape, C == [y = 1-x]) :-
    {X + Y =:= 1},
    ordering(X > Y),
    dump([X,Y], [x,y], C).
test(cyclic_ordering_list, error(cyclic_ordering(_))) :-
    {X + Y =:= 1},
    ordering([X,Y]),
    ordering([Y,X]).
test(cyclic_ordering_lt, error(cyclic_ordering(_))) :-
    {X + Y =:= 1},
    ordering(X < Y),
    ordering(Y < X).
test(cyclic_ordering_after_merge, error(cyclic_ordering(_))) :-
    % each class is acyclic on its own; unifying the variables merges the
    % priority graphs and only then is the result cyclic, so this one is
    % caught by arrangement/2 rather than by ordering/2
    {X + _ =:= 1}, {Y + _ =:= 2},
    ordering(X < Y),
    {A + _ =:= 3}, {B + _ =:= 4},
    ordering(B < A),
    X = A, Y = B,
    dump([X,Y], [x,y], _).
test(ordering_before_constraints, C == [y = 1-x]) :-
    % "ordering/1 acts like a constraint: you can put it anywhere in the
    % computation" (OFAI TR-95-09)
    ordering([Y,X]),
    {X + Y =:= 1},
    dump([X,Y], [x,y], C).
test(ordering_of_three, C == [z = 1-y-x]) :-
    {X + Y + Z =:= 1},
    ordering([Z,Y,X]),
    dump([X,Y,Z], [x,y,z], C).
test(target_must_be_free, error(uninstantiation_error(1))) :-
    {X =:= 1},
    dump([X], [x], _).
test(target_must_be_list, error(type_error(list(var), foo))) :-
    dump(foo, _, _).

:- end_tests(clpq_projection).

%   dump/3 on seeded random systems: six variables, two to nine linear
%   constraints of up to three terms, one to three targets.  Checked
%   against properties every projection has, rather than against
%   recorded output, so the test says nothing about which of several
%   equivalent forms is returned:
%
%     - sound: the system entails every constraint returned;
%     - irredundant: no constraint returned is implied by the others;
%     - tight: each target has the same infimum and supremum under the
%       constraints returned as under the system.
%
%   Fourier-Motzkin elimination has to remove the redundant inequalities
%   it generates, which is what the second catches.

:- begin_tests(clpq_projection_random).

random_system(Seed, Vs, Cs, Ts) :-
    set_random(seed(Seed)),
    length(Vs, 6),
    random_between(2, 9, NC),
    length(Cs, NC),
    maplist(random_constraint(Vs), Cs),
    random_between(1, 3, NT),
    length(Ts0, NT),
    maplist(random_var(Vs), Ts0),
    sort(Ts0, Ts).

random_var(Vs, V) :-
    random_member(V, Vs).

random_constraint(Vs, C) :-
    random_between(1, 3, N),
    length(Terms, N),
    maplist(random_term(Vs), Terms),
    foldl(plus_term, Terms, 0, E),
    random_between(-5, 5, K),
    random_member(Op, [=<, <, >=, >, =<, >=, =:=]),
    C =.. [Op, E, K].

random_term(Vs, K*V) :-
    random_member(K, [-3,-2,-1,1,2,3]),
    random_member(V, Vs).

plus_term(T, E0, E0+T).

%   The projection of a consistent system whose targets are still free.
projection(Seed, Ts, Names, Out) :-
    random_system(Seed, _, Cs, Ts),
    catch(maplist(post, Cs), _, fail),
    maplist(var, Ts),
    length(Ts, L),
    length(Names, L),
    dump(Ts, Names, Out).

post(C) :- {C}.

sound(Ts, Names, Out) :-
    \+ \+ ( Names = Ts,
            forall(member(C, Out), entailed(C)) ).

irredundant(Names, Out) :-
    forall(select(C, Out, Others),
           \+ ( copy_term(Names-(C-Others), _-(C1-Others1)),
                 maplist(post, Others1),
                 entailed(C1) )).

tight(Ts, Names, Out) :-
    forall(nth1(I, Ts, T),
           ( bounds(T, Inf, Sup),
             \+ \+ ( maplist(post, Out),
                     nth1(I, Names, N),
                     bounds(N, Inf, Sup) ) )).

bounds(V, Inf, Sup) :-
    ( inf(V, I) -> Inf = I ; Inf = none ),
    ( sup(V, S) -> Sup = S ; Sup = none ).

%   Seeds 1..1000, and the seeds below 6000 that catch a prefilter/2
%   that ignores the t_lU and t_Lu bound types: the variable is then not
%   eliminated, and the projection is wrong for no other reason.

seed(Seed) :-
    between(1, 1000, Seed).
seed(Seed) :-
    member(Seed, [551, 710, 1213, 2383, 2985, 3666, 4473, 5089, 5606]).

test(projection, [forall(seed(Seed))]) :-
    (   projection(Seed, Ts, Names, Out)
    ->  assertion(sound(Ts, Names, Out)),
        assertion(irredundant(Names, Out)),
        assertion(tight(Ts, Names, Out))
    ;   true                            % inconsistent, or a target bound
    ).

:- end_tests(clpq_projection_random).

		 /*******************************
		 *         RESIDUALS		*
		 *******************************/

:- begin_tests(clpq_residuals).

test(copy_term_bounds, [true(Gs = [{_}]), true(var(Y))]) :-
    {X > 1, X < 3},
    copy_term(X, Y, Gs).
test(copy_term_is_independent, true(var(X))) :-
    {X > 1},
    copy_term(X, Y, Gs),
    maplist(call, Gs),
    {Y =:= 2}.
test(copy_term_unconstrained, Gs == []) :-
    copy_term(_, _, Gs).
test(copy_term_projects_slack_away, Gs = [{A+B>=1}]) :-
    % the slack variable that ineq_more/2 introduces for an inequality
    % over unbounded variables is projected away again
    {X + Y >= 1},
    copy_term(f(X,Y), f(A,B), Gs).
test(copy_term_projects_bounded_slack_away, Extra == []) :-
    % the other branch of ineq_more/2: every variable already has a bound
    {X >= 0, Y >= 0, X + Y >= 1},
    copy_term(f(X,Y), Copy, Gs),
    extra_vars(Gs, Copy, Extra).
test(copy_term_projects_strict_slack_away, Extra == []) :-
    {X >= 0, Y >= 0, X + Y > 1},
    copy_term(f(X,Y), Copy, Gs),
    extra_vars(Gs, Copy, Extra).
test(copy_term_chain_has_no_slack, Extra == []) :-
    {A =< B, B =< C},
    copy_term(f(A,B,C), Copy, Gs),
    extra_vars(Gs, Copy, Extra).
test(copy_term_disequation, Gs = [{A+B=\=1}]) :-
    {X + Y =\= 1},
    copy_term(f(X,Y), f(A,B), Gs).
test(copy_term_nonlinear_has_no_slack, Extra == []) :-
    % the delayed goal of the non-linear part must not drag the slack
    % variable of the linear part back into the answer
    {X * Y =:= Z, X + Y >= 1},
    copy_term(f(X,Y,Z), Copy, Gs),
    extra_vars(Gs, Copy, Extra).
test(copy_term_optimisation_has_no_slack, Extra == []) :-
    % minimize/1 introduces a variable of its own for the objective
    {X >= 1, Y >= 1, X + Y >= 3},
    minimize(X+Y),
    copy_term(f(X,Y), Copy, Gs),
    extra_vars(Gs, Copy, Extra).
test(copy_term_pending_optimisation_has_no_slack, Extra == []) :-
    {Y >= 1, Y =< 5},
    minimize(X*Y),
    copy_term(f(X,Y), Copy, Gs),
    extra_vars(Gs, Copy, Extra).
test(copy_term_equation, true(Gs = [{_}])) :-
    {X + Y =:= 1},
    copy_term(X-Y, _, Gs).
test(pending_optimisation_is_reusable, [X2 == 1, Y2 == 1]) :-
    % a minimize/1 that is still waiting for its expression to become
    % linear is reported as the user level goal that created it, so the
    % answer of copy_term/3 can be executed again
    {Y >= 1, Y =< 5},
    minimize(X*Y),
    copy_term(f(X,Y), f(X2,Y2), Gs),
    assertion(Gs = [{_}, clpq:minimize(_)]),
    maplist(call, Gs),
    {X2 =:= 1}.
test(pending_inf_is_reported, true(Gs = [{_}, clpq:inf(_,_,_,_)])) :-
    {Y >= 1, Y =< 5},
    inf(X*Y, I),
    copy_term(f(X,Y,I), _, Gs).
test(dump_omits_pending_goals, C == [y >= 1, y =< 5]) :-
    % dump/3 returns constraints; a pending optimisation is not one
    {Y >= 1, Y =< 5},
    minimize(_X*Y),
    dump([Y], [y], C).
test(residual_is_reusable, [I == 1, S == 3]) :-
    {X >= 1, X =< 3},
    copy_term(X, Y, Gs),
    maplist(call, Gs),
    inf(Y, I), sup(Y, S).

:- end_tests(clpq_residuals).

% extra_vars(+Goals, +Copy, -Extra)
%
% Extra are the variables of Goals that do not occur in Copy.  A residual
% that mentions a variable the caller cannot see is a slack variable (or
% another solver internal) that projection failed to eliminate.

extra_vars(Goals, Copy, Extra) :-
    term_variables(Goals, GVs),
    term_variables(Copy, CVs),
    sort(GVs, GSet),
    sort(CVs, CSet),
    ord_subtract(GSet, CSet, Extra).

		 /*******************************
		 *        UNIFICATION		*
		 *******************************/

:- begin_tests(clpq_unify).

test(unify_number_ok) :-
    {X >= 1}, X = 2.
test(unify_number_violates, fail) :-
    {X >= 1}, X = 0.
test(unify_rational) :-
    {X >= 1r2}, X = 1r2.
test(unify_float_rejected, error(type_error(rational, 1.5))) :-
    % numbers_only/1 in itf_q.pl only accepts rationals on unification,
    % even though {X =:= 1.5} is fine.
    {X >= 1}, X = 1.5.
test(unify_atom_type_error, error(type_error(rational, a))) :-
    {X >= 1}, X = a.
test(unify_two_constrained) :-
    {X >= 1}, {Y =< 0},
    \+ X = Y.
test(unify_two_constrained_ok, [I == 1, S == 3]) :-
    {X >= 1}, {Y =< 3},
    X = Y,
    inf(X, I), sup(X, S).
test(unify_propagates_equation, X == 1r2) :-
    {X + Y =:= 1},
    X = Y.
test(unify_independent_variable, S == 2) :-
    {X >= 1, Y >= 1, X + Y =< 4},
    X = Y,
    sup(X, S).
test(clp_type_q, T == clpq) :-
    {X > 1},
    clp_type(X, T).
test(clp_type_unconstrained, fail) :-
    clp_type(_, _).
test(mix_clpq_clpr, error(permission_error(_,_,_))) :-
    {X > 1},
    clpr:{X > 2}.
test(mix_clpq_clpr_unify, error(permission_error(_,_,_))) :-
    {X > 1},
    clpr:{Y > 2},
    X = Y.

test(mix_detected_in_inequality_leq, error(permission_error(_,_,_))) :-
    clpr:{X >= 1},
    {X =< 0}.
test(mix_detected_in_inequality_geq, error(permission_error(_,_,_))) :-
    clpr:{X =< 1},
    {X >= 2}.
test(mix_detected_in_strict_upper, error(permission_error(_,_,_))) :-
    clpr:{X >= 1},
    {X < -1}.
test(mix_detected_in_strict_lower, error(permission_error(_,_,_))) :-
    clpr:{X =< 1},
    {X > 2}.
test(mix_detected_in_nonstrict_upper, error(permission_error(_,_,_))) :-
    clpr:{X >= 1},
    {X =< -1}.
test(mix_detected_in_nonstrict_lower, error(permission_error(_,_,_))) :-
    clpr:{X =< 1},
    {X >= 2}.

:- end_tests(clpq_unify).

		 /*******************************
		 *          EXAMPLES		*
		 *******************************/

:- begin_tests(clpq_examples).

% The mortgage relation from the OFAI manual / the Monash examples.
%
%   P  principal, T  periods, I  interest, B  balance, MP  monthly payment

mg(P, T, I, B, MP) :-
    {T = 1, B + MP =:= P * (1 + I)}.
mg(P, T, I, B, MP) :-
    {T > 1, P1 =:= P*(1+I) - MP, T1 =:= T - 1},
    mg(P1, T1, I, B, MP).

% 1000*1.1^3 - 400*(1.1^2+1.1+1) = 1331 - 1324
test(mortgage_forward, B == 7) :-
    mg(1000, 3, 1/10, B, 400),
    !.
test(mortgage_backward, P == 1324000r1331) :-
    mg(P, 3, 1/10, 0, 400),
    !.
test(mortgage_relation, C == [b = 1331r1000*p - 331r100*mp]) :-
    mg(P, 3, 1/10, B, MP),
    !,
    dump([P,B,MP], [p,b,mp], C).

% Fibonacci run backwards; classic CLP(Q) example.

fib(0, 0).
fib(1, 1).
fib(N, F) :-
    {N > 1, N1 =:= N-1, N2 =:= N-2, F =:= F1 + F2},
    fib(N1, F1),
    fib(N2, F2).

test(fib_forward, F == 55) :-
    fib(10, F), !.
test(fib_backward, N == 10) :-
    fib(N, 55), !.

% A small linear program: the "diet" shape.

test(convex_combination, [Min == 1, Max == 9]) :-
    { A >= 0, B >= 0, C >= 0,
      A + B + C =:= 1,
      X =:= 1*A + 4*B + 9*C },
    inf(X, Min), sup(X, Max).

:- end_tests(clpq_examples).

		 /*******************************
		 *      SOLVER INTERNALS	*
		 *******************************/

% Scenarios chosen to exercise paths in bv_q.pl / ineq_q.pl that the
% behavioural tests above do not reach: bounds on fresh variables, bounds
% on *dependent* variables, lower-bound repair (inc_step/2), implied
% bound narrowing and slack introduction.

:- begin_tests(clpq_internals).

test(fresh_strict_upper, [S == 0, true(\+ {X =:= 0})]) :-
    % {X < 0} on a variable the solver has never seen takes the
    % var_intern/3 branch of ineq_one_s_p_0/1
    {X < 0},
    sup(X, S).
test(fresh_strict_lower, [I == 0, true(\+ {X =:= 0})]) :-
    {X > 0},
    inf(X, I).
test(fresh_nonstrict_upper, S == 0) :-
    {X =< 0},
    sup(X, S),
    {X =:= 0}.
test(fresh_nonstrict_lower, I == 0) :-
    {X >= 0},
    inf(X, I),
    {X =:= 0}.
test(ground_inequality_after_aliasing) :-
    % After X and Y are aliased, X-Y =< 1 dereferences to a constant row
    {X =:= Y},
    {X - Y =< 1},
    assertion(\+ {X - Y < 0}),
    {X - Y =< 0}.
test(bound_on_dependent_variable, C == [z >= 1, z =< 3, y = z-x]) :-
    {Z =:= X + Y},
    {Z >= 1, Z =< 3},
    dump([X,Y,Z], [x,y,z], C).
test(strict_bound_on_dependent_variable, C == [z > 1, z < 3]) :-
    {Z =:= _X + _Y},
    {Z > 1, Z < 3},
    dump([Z], [z], C).
test(lower_bound_repair, I == 3) :-
    % Z is basic and below its lower bound, so the solver must *raise* the
    % rhs: this drives inc_step/2 rather than dec_step/2
    {X =< 5, Y =< 5},
    {Z =:= X + Y},
    {Z >= 8},
    inf(X, I).
test(implied_bound_narrowing, S == 1) :-
    % sup(X) is limited to 1 by Y, which the optimiser only finds by
    % pivoting and then narrowing X's upper bound
    {X >= 0, X =< 10, Y >= 0, Y =< 1, X =< Y},
    sup(X, S).
test(unbounded_culprit, S == 99) :-
    {X >= 0},
    {Y =:= X + 1},
    {Y =< 100},
    {X =< 200},
    sup(X, S).
test(two_sided_dump, C == [y = 4-x, x =< 3, x >= 1]) :-
    {X >= 1, X =< 5, Y >= 1, Y =< 5, X + Y =:= 4},
    dump([X,Y], [x,y], C).
test(chained_classes, [B == 1, C == 1, D == 2]) :-
    {A + B =:= 1, B + C =:= 2, C + D =:= 3},
    {A =:= 0}.
test(simplex_three_variables, S == 10) :-
    { X >= 0, Y >= 0, Z >= 0,
      X + Y + Z =< 10,
      X + 2*Y =< 8,
      Y + 3*Z =< 9 },
    sup(X + Y + Z, S).
test(strict_slack, [S == 1, true(\+ {X =:= 1})]) :-
    {X + Y < 1, X > 0, Y > 0},
    sup(X, S).
test(equality_inside_bounds, X == 3) :-
    {X >= 1, X =< 5},
    {X =:= 3}.
test(equality_outside_bounds) :-
    {X >= 1, X =< 5},
    \+ {X =:= 6}.
test(nonzero_on_expression, C == [x+y =\= 1]) :-
    {X + Y =\= 1},
    dump([X,Y], [x,y], C).
test(nonzero_with_bound) :-
    {X =\= 0},
    {X >= 0},
    \+ {X =:= 0}.
test(fourier_motzkin_chain, C == [x-w =< 0]) :-
    {X =< Y, Y =< Z, Z =< W},
    dump([X,W], [x,w], C).
test(fourier_motzkin_two_sided, C == [x >= -1, x =< 11]) :-
    {X - Y =< 1, Y - X =< 1, Y >= 0, Y =< 10},
    dump([X], [x], C).

% Eliminating a variable adds inequalities that may be redundant, and
% only those are checked for redundancy; x =< 5 is generated from
% x =< y, y =< 5 and is implied by x =< 3.
test(fourier_motzkin_new_row_redundant, C == [x =< 3]) :-
    {X =< Y, Y =< 5, X =< 3},
    dump([X], [x], C).
test(fourier_motzkin_longer_chain, C == [a-e =< 0]) :-
    {A =< B, B =< C0, C0 =< D, D =< E},
    dump([A,E], [a,e], C).
% The variables to eliminate are in two classes.
test(fourier_motzkin_two_classes, C == [u >= 2, x =< 1]) :-
    {X =< Y, Y =< 1, U >= V, V >= 2},
    dump([X,U], [x,u], C).
test(fourier_motzkin_strict, C == [x < 4]) :-
    {X < Y, Y =< Z, Z < 4},
    dump([X], [x], C).
% Two variables to eliminate, each generating as many inequalities.
test(fourier_motzkin_cycle, C == [x >= -2, x =< 12]) :-
    {X - Y =< 1, Y - Z =< 1, Z - X =< 1, Y >= 0, Z =< 10},
    dump([X], [x], C).
test(redundant_two_sided, C == [x >= 1, x =< 5]) :-
    {X >= 1, X =< 5, X >= 0, X =< 10},
    dump([X], [x], C).
test(redundant_strictness, C == [x > 1, x < 5]) :-
    {X > 1, X >= 1, X < 5, X =< 5},
    dump([X], [x], C).
test(maximize_then_constrain) :-
    {X >= 1, X =< 5},
    maximize(X),
    {X =:= 5}.

% Aliasing two variables that carry different bound types makes
% attr_unify_hook/2 re-post the bounds of one on the other
% (verify_type_var/5 and friends in itf_q.pl).

test(alias_upper_with_lower, [I == 0, S == 5]) :-
    {X =< 5}, {Y >= 0},
    X = Y,
    inf(X, I), sup(X, S).
test(alias_two_intervals, [I == 2, S == 5]) :-
    {X >= 1, X =< 5}, {Y >= 2, Y =< 9},
    X = Y,
    inf(X, I), sup(X, S).
test(alias_strict_bounds, [true(\+ {X =:= 1}), true(\+ {X =:= 5})]) :-
    {X > 1}, {Y < 5},
    X = Y.
test(alias_strict_intervals, C == [x > 1, x < 5]) :-
    {X > 1, X < 9}, {Y > 0, Y < 5},
    X = Y,
    dump([X], [x], C).
test(alias_after_pivoting, I == 2) :-
    {X >= 1, Y >= 1, X + Y =< 4},
    sup(X, _),
    {Z >= 2},
    X = Z,
    inf(X, I).

% Several delayed goals on one variable exercise the conjunction cases of
% geler.pl's trans//1 and transg//1.

test(two_delayed_goals, [Y == 3, Z == 6]) :-
    {X*Y =:= 6},
    {X*Z =:= 12},
    {X =:= 2}.
test(two_delayed_goals_residual, true(Gs = [{_}])) :-
    {X*_Y =:= 6},
    {X*_Z =:= 12},
    copy_term(X, _, Gs).
test(nonlinear_residual_is_reported_once, true(Gs = [{_}])) :-
    % every variable of a purely non-linear store carries the same delayed
    % goal; attribute_goals//1 must report the conjunction only once
    {X*Y =:= 6},
    copy_term(X-Y, _, Gs).
test(unrelated_stores_are_reported_separately, true(Gs = [{_},{_}])) :-
    {X*Y =:= 6},
    {A + B =:= 1},
    copy_term(f(X,Y,A,B), _, Gs).
test(alias_delayed_variables, all(X == [2,-2])) :-
    % aliasing turns X*Y =:= 4 into X^2 =:= 4, which is now solved
    {X*Y =:= 4},
    X = Y.
test(alias_delayed_variables_irrational, fail) :-
    {X*Y =:= 6},
    X = Y.
test(alias_across_delayed_goals, [Y == 3, W == 4]) :-
    {X*Y =:= 6},
    {Z*W =:= 12},
    Y = Z,
    {X =:= 2}.

% Projections that leave active bounds and mixed strictness behind,
% exercising the t_L/t_U/t_Lu/t_lU cases of redund.pl.

test(project_strict_system, C == [x < 10, x > 0]) :-
    {X > 0, Y > 0, X + Y < 10, X - Y > -5},
    dump([X], [x], C).
test(project_with_equality, C == [x-y =< 0, x+y =< 1, x >= 0]) :-
    {X >= 0, Y >= 0, Z >= 0, X + Y + Z =:= 1, X =< Y},
    dump([X,Y], [x,y], C).
test(project_mixed_strictness, C == [y = 4-x, x < 3, x >= 1]) :-
    {X >= 1, X < 5, Y > 1, Y =< 5, X + Y =:= 4},
    dump([X,Y], [x,y], C).
test(project_after_optimisation, C == [y >= 1, x+y =< 6, x >= 1]) :-
    {X >= 1, Y >= 1, X + Y =< 6},
    sup(X + Y, _),
    dump([X,Y], [x,y], C).
test(project_strict_interval, C == [y > 0, x+y =< 5, x > 0]) :-
    {X > 0, X < 10, Y > 0, Y < 10, X + Y =< 5},
    dump([X,Y], [x,y], C).

% Ground evaluation of the non-linear functions (nl_eval/2).

test(eval_sin, X == 0) :-
    {X =:= sin(0)}.
test(eval_cos, X == 1) :-
    {X =:= cos(0)}.
test(eval_tan, X == 0) :-
    {X =:= tan(0)}.

% Trivially true and trivially false ground inequalities.

test(ground_leq) :-
    {0 =< 0}.
test(ground_geq) :-
    {1 >= 1}.
test(ground_lt, fail) :-
    {0 < 0}.

% Non-linear comparisons other than equality are delayed too.

test(nonlinear_lt_delayed, true((var(X),var(Y)))) :-
    {X*Y < 0}.
test(nonlinear_le_delayed, true(var(X))) :-
    {X*_Y =< 0}.
test(nonlinear_eq_zero_delayed, true(var(X))) :-
    {X*_Y =:= 0}.
test(nonlinear_lt_woken, [C == [y < 3]]) :-
    {X*Y < 6},
    {X =:= 2},
    dump([Y], [y], C).

% Residual goals for each kind of delayed constraint (transg//1).

test(residual_nonlinear_le, C == [-6 + y*x =< 0]) :-
    {X*Y =< 6},
    dump([X,Y], [x,y], C).
test(residual_nonlinear_lt, C == [-6 + y*x < 0]) :-
    {X*Y < 6},
    dump([X,Y], [x,y], C).
test(residual_nonlinear_ne, C == [-6 + y*x =\= 0]) :-
    {X*Y =\= 6},
    dump([X,Y], [x,y], C).
test(residual_negative_exponent, C == [x - 1/y = 0]) :-
    {X =:= 1/Y},
    dump([X,Y], [x,y], C).
test(residual_square, C == [-2 + x + x^2 = 0]) :-
    {X*X + X =:= 2},
    dump([X], [x], C).
test(residual_nested_function, C == [x - sin(1+y) = 0]) :-
    {X =:= sin(Y+1)},
    dump([X,Y], [x,y], C).

% Optimisation of an expression that is not yet linear waits
% (wait_linear_retry/3).

test(minimize_waits_for_linear, [X == 1, Y == 1]) :-
    {Y >= 1, Y =< 5},
    minimize(X*Y),
    {X =:= 1}.
test(inf_of_nonlinear_waits, [I == 1]) :-
    {Y >= 1, Y =< 5},
    inf(X*Y, I),
    {X =:= 1}.

% Division by a non-constant stays as an undigested quotient until the
% divisor is known (nf_div/3 third clause, repair_p_one/2).

test(division_by_expression, [X == 1r2]) :-
    {X =:= 1/(Y+1)},
    {Y =:= 1}.

% Wide expressions take the recursive (N>2) branches of the logarithmic
% helpers nf_mul_log/6, nf_mul_factor_log/5, repair_log/4, repair_p_log/6.

test(wide_product, [Z == 25]) :-
    {Z =:= (A+B+C+D+E)*(A+B+C+D+E)},
    {A =:= 1, B =:= 1, C =:= 1, D =:= 1, E =:= 1}.
test(wide_repair, [Z == 44]) :-
    {Z =:= A*B + C*D + E*F},
    {A =:= 1, B =:= 2, C =:= 3, D =:= 4, E =:= 5, F =:= 6}.
test(entailed_disequation) :-
    {X =:= 4},
    entailed(X =\= 3).

% --- gaps found by reading the annotated coverage sources ---

test(row_cancellation, [X == 2, A == 3, B == 1]) :-
    % back-substitution makes Y's coefficient vanish inside
    % add_linear_11h/6; the rest of the suite only cancels in the
    % normal form, which is a different code path
    {A =:= X + Y},
    {B =:= X - Y},
    {A + B =:= 4},
    {Y =:= 1}.
test(row_cancellation_to_constant, X == 3) :-
    {Z =:= X + Y},
    {W =:= 0 - Y},
    {Z + W =:= 3}.
test(leading_coefficient_minus_one, C == [y = -x]) :-
    % exercises the K =:= -1 arms of nf2sum/3 and f02t/2
    {X + Y =:= 0},
    dump([X,Y], [x,y], C).
test(nonzero_variable_becomes_linear, Y == 4) :-
    % X = Y gives Y a clpqr_itf attribute that carries only the nonzero
    % mark and no linear equation, which deref_var/2 then has to fill in
    {X =\= 3},
    X = Y,
    {Y + Z =:= 5},
    {Z =:= 1}.
test(nonzero_variable_still_checked, fail) :-
    {X =\= 3},
    X = Y,
    {Y + Z =:= 5},
    {Z =:= 2}.
test(mix_detected_in_inequality, error(permission_error(_,_,_))) :-
    % the solver-mixing check inside ineq_one_s_p_0/1 rather than the one
    % in deref_var/2
    clpr:{X >= 1},
    {X < 0}.
test(mix_detected_in_inequality_lower, error(permission_error(_,_,_))) :-
    clpr:{X >= 1},
    {X > 0}.
test(exponent_cancellation, Y == 1) :-
    % X^1 * X^-1 cancels in pmerge_case/9
    {Y =:= X * (1/X)}.
test(optimisation_redelayed, [true(var(Z))]) :-
    % the expression is still non-linear when the delayed goal wakes, so
    % wait_linear_retry/3 has to delay it again
    {X*Y*Z >= 1},
    minimize(X*Y*Z),
    {X =:= 1}.

test(residual_leading_coefficient, C == [2*(x*y) =< 0]) :-
    % f02t/2's K =\= 1 arms: a delayed goal whose first monomial is scaled
    {2*X*Y =< 0},
    dump([X,Y], [x,y], C).
test(residual_leading_negation, C == [-(y*x) =< 0]) :-
    {-(X*Y) =< 0},
    dump([X,Y], [x,y], C).
test(row_cancellation_in_merge, [A == 7, B == (-7)]) :-
    % three monomials make log_deref/4 split and merge the halves with
    % add_linear_11/3, where the X terms cancel
    {A =:= X}, {B =:= 0-X}, {C =:= 0},
    {A + B + C =:= 0},
    assertion(var(X)),
    {X =:= 7}.
test(row_cancellation_in_merge_2, true((var(X),var(Y)))) :-
    {A =:= X+Y}, {B =:= 0-X}, {C =:= 0-Y},
    {A + B + C =:= 0}.
test(renormalize_over_bound_variable, C == [z = 1-y]) :-
    % ordering/1 forces arrange/2, which renormalizes every row; one of the
    % class variables is already bound to a number
    {X + Y + Z =:= 1}, {X =:= 0},
    ordering([Z,Y]),
    dump([Y,Z], [y,z], C).

:- end_tests(clpq_internals).

		 /*******************************
		 *      TOPLEVEL PRINTING	*
		 *******************************/

% The residual constraints the toplevel prints for a query come from
% clpq.pl's own prolog:message//1 hook rather than from attribute_goals//1.

:- begin_tests(clpq_toplevel).

test(bounds, C == ['X' > 3]) :-
    {X > 3},
    clpq:dump_toplevel_bindings(['X'=X], C).
test(equation, C == ['Y' = 1-'X']) :-
    {X + Y =:= 1},
    clpq:dump_toplevel_bindings(['X'=X,'Y'=Y], C).
test(nonlinear, C == [-6 + 'Y'*'X' = 0]) :-
    {X*Y =:= 6},
    clpq:dump_toplevel_bindings(['X'=X,'Y'=Y], C).
test(same_variable_reported_once, C == ['A' > 3]) :-
    % a variable bound to two names must be dumped only once
    {X > 3},
    clpq:dump_toplevel_bindings(['A'=X,'B'=X], C).
test(unconstrained, C == []) :-
    clpq:dump_toplevel_bindings(['X'=_], C).
test(nonvar_binding, C == []) :-
    clpq:dump_toplevel_bindings(['X'=foo], C).

:- end_tests(clpq_toplevel).

		 /*******************************
		 *        KNOWN ISSUES		*
		 *******************************/

:- begin_tests(clpq_known_issues).

% See doc/design.md, section 14.  These tests pin down *wrong* behaviour so
% that fixing it is noticed.  Each says what the right answer would be.

test(division_by_zero_does_not_raise, fail) :-
    % zero_division/0 is `fail' with the comment `% raise_exception(_) ?'.
    % An evaluation_error(zero_divisor) would be more useful.
    {_ =:= 1/0}.

:- end_tests(clpq_known_issues).
