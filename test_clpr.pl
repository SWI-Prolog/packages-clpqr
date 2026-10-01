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

:- module(test_clpr,
          [ test_clpr/0
          ]).
:- use_module(library(plunit)).
:- use_module(library(lists)).
:- use_module(library(ordsets)).
:- use_module(library(clpr)).
:- use_module(library(clpq), []).          % for the solver-mixing tests

/** <module> Test CLP(R)

Tests for library(clpr).  The structure follows doc/design.md and mirrors
test_clpq.pl, with extra units for the features that only exist in CLP(R)
(symbolic constants, root extraction, the epsilon of bb_inf/5) and for the
consequences of computing with floats.

Numeric results are compared with =near/2=, which uses the solver's own
epsilon of 1.0e-10.

@see doc/design.md
*/

test_clpr :-
    run_tests([ clpr_syntax,
                clpr_nf,
                clpr_equations,
                clpr_inequalities,
                clpr_disequations,
                clpr_nonlinear,
                clpr_entailment,
                clpr_optimisation,
                clpr_bb,
                clpr_projection,
                clpr_residuals,
                clpr_unify,
                clpr_internals,
                clpr_examples,
                clpr_toplevel,
                clpr_known_issues
              ]).

%!  near(+X, +Y) is semidet.
%
%   True when X and Y are equal within the solver's own epsilon.

near(X, Y) :-
    NX is X,
    NY is Y,
    abs(NX-NY) =< 1.0e-10.

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

:- begin_tests(clpr_syntax).

test(conjunction, true(near(X, 2.0))) :-
    {X > 1, X < 3, X =:= 2}.
test(nested_conjunction, [true(near(X,1.0)), true(near(Y,2.0))]) :-
    {(X =:= 1, Y =:= 2)}.
test(disjunction, all(Ok == [true,true])) :-
    {X =:= 1 ; X =:= 2},
    ( near(X,1.0) ; near(X,2.0) ),
    Ok = true.
test(less) :-
    {X < 3, X > 2, X =:= 2.5}.
test(greater) :-
    {3 > X, 2 < X, X =:= 2.5}.
test(leq, true(near(X, 3.0))) :-
    {X =< 3, X >= 3}.
test(leq_alt, true(near(X, 3.0))) :-
    {<=(X, 3)}, {X >= 3}.
test(eq_is, true(near(X, 3.0))) :-
    {X =:= 3}.
test(eq_unify, true(near(X, 3.0))) :-
    {X = 3}.
test(result_is_float, true(float(X))) :-
    {X =:= 3}.
test(unary_minus, true(near(X, 3.0))) :-
    {X =:= -(-3)}.
test(unary_plus, true(near(X, 3.0))) :-
    {X =:= +3}.
test(division, true(near(X, 0.25))) :-
    {X =:= 1/4}.
test(abs, true(near(X, 7.0))) :-
    {X =:= abs(-7)}.
test(min, true(near(X, 3.0))) :-
    {X =:= min(3,4)}.
test(max, true(near(X, 4.0))) :-
    {X =:= max(3,4)}.
test(pow, true(near(X, 1024.0))) :-
    {X =:= pow(2,10)}.
test(hat, true(near(X, 1024.0))) :-
    {X =:= 2^10}.
test(exp2, true(near(X, 1024.0))) :-
    {X =:= exp(2,10)}.
test(negative_power, true(near(X, 0.25))) :-
    {X =:= 2^(-2)}.
test(zero_power, true(near(X, 1.0))) :-
    {X =:= 5^0}.
test(fractional_power, true(near(X, 1.4142135623730951))) :-
    {X =:= 2^0.5}.

% Symbolic "Monash" constants; CLP(R) only.

test(constant_pi, true(near(X, pi))) :-
    {X =:= #(pi)}.
test(constant_p, true(near(X, pi))) :-
    {X =:= #(p)}.
test(constant_e, true(near(X, e))) :-
    {X =:= #(e)}.
test(constant_zero, true(near(X, 1.0e-10))) :-
    {X =:= #(zero)}.

% Errors

test(var_constraint, error(instantiation_error)) :-
    {_}.
test(bad_constraint, error(type_error(clpr_constraint, foo))) :-
    {foo}.
test(bad_expression, error(type_error(clpr_expression, a))) :-
    {_ =:= a}.
test(star_star_rejected, error(type_error(clpr_expression, 2**3))) :-
    {_ =:= 2**3}.
test(sqrt_rejected, error(type_error(clpr_expression, sqrt(4)))) :-
    {_ =:= sqrt(4)}.
test(unknown_constant_rejected, error(type_error(clpr_expression, #(foo)))) :-
    {_ =:= #(foo)}.
test(entailed_var, error(instantiation_error)) :-
    entailed(_).
test(entailed_bad, error(type_error(clpr_constraint, foo))) :-
    entailed(foo).
test(bb_inf_bad_int, error(type_error(var, _))) :-
    {X >= 0},
    bb_inf([_+_], X, _).

:- end_tests(clpr_syntax).

		 /*******************************
		 *        NORMAL FORM		*
		 *******************************/

:- begin_tests(clpr_nf).

test(cancel) :-
    {X - X =:= 0}, var(X).
test(cancel_sum, true(near(Y, 1.0))) :-
    {Y =:= X + 1 - X}.
test(collect, true(near(Y, 0.0))) :-
    {Y =:= 2*X + 3*X - 5*X}.
test(distribute, true(near(Y, -1.0))) :-
    {Y =:= (X+1)*(X-1) - X*X}.
test(binomial, true(near(Y, 1.0))) :-
    {Y =:= (X+1)^2 - X^2 - 2*X}.
test(binomial_big, true(near(Y, 0.0))) :-
    {Y =:= (1+X)^3 - (1 + 3*X + 3*X^2 + X^3)}.
test(scalar_product, true(near(X, 12.0))) :-
    {X =:= 3*4}.
test(division_by_variable_is_nonlinear, true(var(X))) :-
    {_ =:= 1/X}.
test(division_by_zero_fails, fail) :-
    {_ =:= 1/0}.
test(mult_two_vars_is_nonlinear, true((var(X),var(Y),var(Z)))) :-
    {Z =:= X*Y}.
test(mult_by_constant_is_linear, true(near(Z, 6.0))) :-
    {Z =:= 3*X, X =:= 2}.
test(zero_snapping, X == 0.0) :-
    % export_binding/2 snaps a result within epsilon of 0 to exactly 0.0
    {X =:= 1.0e-15}.

:- end_tests(clpr_nf).

		 /*******************************
		 *          EQUATIONS		*
		 *******************************/

:- begin_tests(clpr_equations).

test(two_by_two, [true(near(X, 2.0)), true(near(Y, 1.0))]) :-
    {2*X + 3*Y =:= 7, X - Y =:= 1}.
test(three_by_three,
     [ true(near(X, 1.0))
     , true(near(Y, 2.0))
     , true(near(Z, 3.0))
     ]) :-
    { X + Y + Z =:= 6,
      X - Y + Z =:= 2,
      X + Y - Z =:= 0 }.
test(fractional_solution, true(near(X, 1/3))) :-
    {3*X =:= 1}.
test(inconsistent, fail) :-
    {X + Y =:= 1, X + Y =:= 2}.
test(dependent_rows, true((var(X),var(Y)))) :-
    {X + Y =:= 1, 2*X + 2*Y =:= 2}.
test(implied_value, [true(near(X, 2.0)), true(near(Y, 1.0))]) :-
    {X + Y =:= 3},
    assertion((var(X),var(Y))),
    {X - Y =:= 1}.
test(class_merge,
     [ true(near(Y, 1.0))
     , true(near(Z, 1.0))
     , true(near(W, 1.0))
     ]) :-
    {X + Y =:= 1},
    {Z + W =:= 2},
    {Y =:= Z},
    {X =:= 0}.
test(alias, true(near(Y, 1.0))) :-
    {X =:= Y}, {X =:= 1}.
test(chain, true(near(A, 7.0))) :-
    {A =:= B, B =:= C, C =:= D, D =:= 7}.
test(negative_coefficients, [true(near(X, 2.0)), true(near(Y, 1.0))]) :-
    {-X - Y =:= -3, X - Y =:= 1}.

:- end_tests(clpr_equations).

		 /*******************************
		 *        INEQUALITIES		*
		 *******************************/

:- begin_tests(clpr_inequalities).

test(simple_bounds, [true(near(I, 1.0)), true(near(S, 3.0))]) :-
    {X >= 1, X =< 3},
    assertion(var(X)),
    inf(X, I), sup(X, S).
test(meeting_bounds, true(near(X, 2.0))) :-
    {X >= 2, X =< 2}.
test(strict_meeting_bounds, fail) :-
    {X > 2, X =< 2}.
test(strict_both, fail) :-
    {X > 2, X < 2}.
test(empty_interval, fail) :-
    {X >= 3, X =< 2}.
test(tighten_lower, [true(entailed(X >= 2)), true(\+ entailed(X >= 3))]) :-
    {X >= 1}, {X >= 2}, {X >= 0}.
test(tighten_upper, [true(entailed(X =< 3)), true(\+ entailed(X =< 2))]) :-
    {X =< 5}, {X =< 3}, {X =< 9}.
test(strictness_kept, [true(\+ {X =:= 1}), true(entailed(X >= 1))]) :-
    {X > 1}.
test(two_variables, true(near(S, 10.0))) :-
    {X + Y =< 10, X >= 0, Y >= 0},
    sup(X, S).
test(triangle, true(near(Y, 0.0))) :-
    {X >= 0, Y >= 0, X + Y =< 1},
    assertion(\+ {X =:= 1, Y =:= 1}),
    {X =:= 1}.
test(unbounded_sup, fail) :-
    {X >= 0},
    sup(X, _).
test(unbounded_inf, fail) :-
    {X =< 0},
    inf(X, _).
test(transitive, [true(near(Y, 1.0)), true(near(Z, 1.0))]) :-
    {X =< Y, Y =< Z, Z =< X},
    {X =:= 1}.
test(transitive_strict, fail) :-
    {X < Y, Y < Z, Z < X}.
test(slack_elimination,
     [ true(near(A, 1.0))
     , true(near(B, 1.0))
     , true(near(C, 1.0))
     , true(near(D, 1.0))
     ]) :-
    { A >= 0, B >= 0, C >= 0, D >= 0,
      A + B + C + D =< 4,
      A + B + C + D >= 4,
      A =< 1, B =< 1, C =< 1, D =< 1 }.
test(negative_bounds, true(near(S, -5.0))) :-
    {X =< -5},
    assertion(entailed(X < 0)),
    sup(X, S).
test(scaled_bound, true(near(S, 7/3))) :-
    {3*X =< 7},
    sup(X, S).
test(mixed_eq_ineq, [true(near(I, 0.0)), true(near(S, 10.0))]) :-
    {X + Y =:= 10, X >= 0, Y >= 0},
    inf(X, I), sup(X, S).
test(epsilon_tolerance, true(near(X, 1.0))) :-
    % Differences below 1.0e-10 are not distinguished
    {X >= 1, X =< 1 + 1.0e-15}.

:- end_tests(clpr_inequalities).

		 /*******************************
		 *        DISEQUATIONS		*
		 *******************************/

:- begin_tests(clpr_disequations).

test(ground_true) :-
    {1 =\= 2}.
test(ground_false, fail) :-
    {1 =\= 1}.
test(delayed_ok, true(near(X, 4.0))) :-
    {X =\= 3},
    {X =:= 4}.
test(delayed_violated, fail) :-
    {X =\= 3},
    {X =:= 3}.
test(delayed_violated_unify, fail) :-
    {X =\= 3},
    X = 3.0.
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
test(residual_shape, true(near(V, 3.0))) :-
    {X =\= 3},
    dump([X], [x], C),
    C = [x =\= V].

:- end_tests(clpr_disequations).

		 /*******************************
		 *         NON-LINEAR		*
		 *******************************/

:- begin_tests(clpr_nonlinear).

test(spent_goals_are_not_retained, [Live == 4, Spent == 0]) :-
    % unifying two variables that both carry delayed goals runs those
    % goals; they must not stay attached to the survivor.  geler.pl said
    % del_attr(Y,geler) where the attribute is named clpqr_geler, so the
    % spent goals were never dropped and the conjunction grew as N^2.
    {A*_ =:= 1}, {B*_ =:= 2}, {C*_ =:= 3}, {D*_ =:= 4},
    A = B, A = C, A = D,
    geler_goals(A, Live, Spent).
test(waking_is_deterministic, [Det == true, true(near(Y, 3.0))]) :-
    % waking a delayed goal used to leave a choice point behind, in
    % geler.pl's run/2 and attr_unify_hook/2 and in nf_r.pl's repair_p/5
    {X*Y =:= 6},
    det_call({X =:= 2}, Det).
test(delayed_product, [true(near(Y, 3.0))]) :-
    {X*Y =:= 6},
    assertion((var(X), var(Y))),
    {X =:= 2}.
test(delayed_product_other_way, [true(near(X, 2.0))]) :-
    {X*Y =:= 6},
    {Y =:= 3}.
test(division_delayed, [true(near(X, 6.0))]) :-
    {X/Y =:= 2},
    {Y =:= 3}.
test(abs_delayed, [true(near(X, 4.0))]) :-
    {X =:= abs(Y)},
    {Y =:= -4}.
test(min_delayed, [true(near(X, 1.0))]) :-
    {X =:= min(Y,3)},
    {Y =:= 1}.
test(max_delayed, [true(near(X, 5.0))]) :-
    {X =:= max(Y,3)},
    {Y =:= 5}.
test(invert_sin, true(near(X, 0.0))) :-
    {0 =:= sin(X)}.
test(invert_cos, true(near(X, 0.0))) :-
    {1 =:= cos(X)}.
test(invert_tan, true(near(X, 0.0))) :-
    {0 =:= tan(X)}.
test(invert_asin, true(near(X, pi/2))) :-
    {1 =:= sin(X)}.
test(invert_exponent, true(near(Y, 3.0))) :-
    % 2^Y = 8; CLP(R) gets this exactly right, CLP(Q) does not
    {8 =:= 2^Y}.
test(root_odd, true(near(Y, 2.0))) :-
    % isolation axiom: X and Z ground in X = Y^Z
    {8 =:= Y^3}.
test(root_odd_negative, true(near(Y, -2.0))) :-
    {-8 =:= Y^3}.
test(root_even, all(Ok == [true,true])) :-
    % an even root has two solutions and CLP(R) enumerates both
    {4 =:= Y^2},
    ( near(Y, 2.0) ; near(Y, -2.0) ),
    Ok = true.
test(square_is_solved, [nondet, true(near(X, 1.4142135623730951))]) :-
    % unlike CLP(Q), this binds X
    {X*X =:= 2}.
test(nonlinear_becomes_linear, [true(near(Z, 1.0))]) :-
    {Z =:= X*_Y + 1},
    {X =:= 0}.
test(goal_runs_once) :-
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
test(power_of_variable_delayed, [true(near(Y, 8.0))]) :-
    {Y =:= X^3},
    {X =:= 2}.

:- end_tests(clpr_nonlinear).

		 /*******************************
		 *         ENTAILMENT		*
		 *******************************/

:- begin_tests(clpr_entailment).

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

:- end_tests(clpr_entailment).

		 /*******************************
		 *        OPTIMISATION		*
		 *******************************/

:- begin_tests(clpr_optimisation).

test(inf_simple, true(near(I, 1.0))) :-
    {X >= 1, X =< 5},
    inf(X, I).
test(sup_simple, true(near(S, 5.0))) :-
    {X >= 1, X =< 5},
    sup(X, S).
test(inf_does_not_bind, true(near(S, 5.0))) :-
    {X >= 1, X =< 5},
    inf(X, _),
    assertion(var(X)),
    sup(X, S).
test(inf_expression, true(near(I, 2.0))) :-
    {X >= 1, Y >= 1, X + Y =< 4},
    inf(X + Y, I).
test(sup_expression, true(near(S, 4.0))) :-
    {X >= 1, Y >= 1, X + Y =< 4},
    sup(X + Y, S).
test(inf_vertex, [true(near(I,2.0)), true(near(A,1.0)), true(near(B,1.0))]) :-
    {X >= 1, Y >= 1, X + Y =< 4},
    inf(X + Y, I, [X,Y], V),
    V = [A,B].
test(minimize, true(near(X, 2.0))) :-
    {X >= 2, X =< 7},
    minimize(X).
test(maximize, true(near(X, 7.0))) :-
    {X >= 2, X =< 7},
    maximize(X).
test(minimize_expression, [true(near(X, 1.0)), true(near(Y, 1.0))]) :-
    {X >= 1, Y >= 1, X + Y =< 4},
    minimize(X + Y).
test(maximize_expression, true(entailed(X + Y =:= 4))) :-
    {X >= 1, Y >= 1, X + Y =< 4},
    maximize(X + Y).
test(lp_diet, true(near(I, 6.8))) :-
    { A >= 0, B >= 0,
      A + 2*B >= 4,
      3*A + B >= 6 },
    inf(2*A + 3*B, I).
test(unbounded_inf_fails, fail) :-
    {X >= 0},
    inf(-X, _).
test(does_not_touch_global_variables, [true(near(I, 1.0)), V == mine]) :-
    nb_setval(inf, mine),
    {X >= 1, X =< 5},
    inf(X, I),
    nb_getval(inf, V),
    nb_delete(inf).
test(inf_waits_for_linear, [true(near(I, 3.0))]) :-
    {X*Y >= 3},
    {X =:= 1},
    inf(Y, I).

:- end_tests(clpr_optimisation).

		 /*******************************
		 *      BRANCH AND BOUND	*
		 *******************************/

:- begin_tests(clpr_bb).

test(single_variable, true(near(I, 1.0))) :-
    {X >= 0.5, X =< 3.5},
    bb_inf([X], X, I).
test(single_variable_vertex, [true(near(I, 1.0)), V == [1]]) :-
    {X >= 0.5, X =< 3.5},
    bb_inf([X], X, I, V, 0.001).
test(two_variables, true(near(I, 1.0))) :-
    {X >= 0, Y >= 0, X + Y >= 1},
    bb_inf([X,Y], X + Y, I).
test(fractional_optimum, true(near(I, 1.0))) :-
    {2*X >= 1, X >= 0},
    bb_inf([X], X, I).
test(does_not_bind, true(near(LpInf, 0.5))) :-
    {X >= 0.5, X =< 3.5},
    bb_inf([X], X, _),
    assertion(var(X)),
    inf(X, LpInf).
test(knapsack, true(near(I, 3.0))) :-
    { A >= 0, B >= 0,
      A =< 3, B =< 3,
      2*A + 3*B >= 7 },
    bb_inf([A,B], A + B, I).
test(objective_not_integral, true(near(I, 1.25))) :-
    {X >= 0.5, Y >= 0.25},
    bb_inf([X], X + Y, I).
test(ground_integer_ok, true(near(I, 0.0))) :-
    {X >= 0},
    bb_inf([2], X, I).
test(ground_noninteger_fails, fail) :-
    {X >= 0},
    bb_inf([1.5], X, _).
test(unbounded_fails, fail) :-
    {X >= 0},
    bb_inf([X], -X, _).
test(does_not_touch_global_variables, [true(near(I, 1.0)), V == mine]) :-
    nb_setval(prov_opt, mine),
    {X >= 0.5, X =< 3.5},
    bb_inf([X], X, I),
    nb_getval(prov_opt, V),
    nb_delete(prov_opt).
test(bounds_are_narrowed_to_integers, true(near(I, 2.0))) :-
    % bb_intern/4 first narrows the *bounds* of each integer variable to
    % enclosing integers, independently of Eps
    {X >= 1.9999, X =< 5},
    bb_inf([X], X, I, _, 0.001).
test(epsilon_accepts_near_integer, true(near(I, 1.9999))) :-
    % a ground value within Eps of an integer is accepted as integral
    {X =:= 1.9999},
    bb_inf([X], X, I, _, 0.001).
test(small_epsilon_rejects_near_integer, fail) :-
    % ... and rejected when Eps is tight
    {X =:= 1.9999},
    bb_inf([X], X, _, _, 1.0e-9).

test(ground_objective, true(near(I, 3.0))) :-
    {X =:= 3},
    bb_inf([X], X, I).

:- end_tests(clpr_bb).

		 /*******************************
		 *         PROJECTION		*
		 *******************************/

:- begin_tests(clpr_projection).

test(empty, C == []) :-
    dump([], [], C).
test(unconstrained, C == []) :-
    dump([_], [x], C).
test(equation, true(C = [y = 1.0-x])) :-
    {X + Y =:= 1},
    dump([X,Y], [x,y], C).
test(bounds, [true(near(L,1.0)), true(near(U,3.0))]) :-
    {X >= 1, X =< 3},
    dump([X], [x], C),
    C = [x >= L, x =< U].
test(strict_bounds, true(C = [x > _, x < _])) :-
    {X > 1, X < 3},
    dump([X], [x], C).
test(redundant_bounds_removed, true(near(L, 2.0))) :-
    {X >= 1, X >= 2, X >= 0},
    dump([X], [x], C),
    C = [x >= L].
test(projection_eliminates_variable, C == []) :-
    {X + Y >= 1, Y >= 0},
    dump([X], [x], C).
test(fourier_motzkin, true(C = [x-z =< _])) :-
    {X =< Y, Y =< Z},
    dump([X,Z], [x,z], C).
test(does_not_change_store, [true(near(I,1.0)), true(near(S,3.0))]) :-
    {X >= 1, X =< 3},
    dump([X], [x], _),
    inf(X, I), sup(X, S).
test(nonlinear_residue, true(C = [_])) :-
    {X*Y =:= 6},
    dump([X,Y], [x,y], C).
test(target_order_does_not_control_shape, C1 == C2) :-
    {X + Y =:= 1},
    dump([X,Y], [x,y], C1),
    dump([Y,X], [y,x], C2).
test(ordering_list_controls_shape, true(C = [y = _-x])) :-
    % the variable that comes first is the one the answer defines
    {X + Y =:= 1},
    ordering([Y,X]),
    dump([X,Y], [x,y], C).
test(ordering_list_controls_shape_2, true(C = [x = _-y])) :-
    {X + Y =:= 1},
    ordering([X,Y]),
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
test(ordering_before_constraints, true(C = [y = _-x])) :-
    ordering([Y,X]),
    {X + Y =:= 1},
    dump([X,Y], [x,y], C).
test(target_must_be_free, error(uninstantiation_error(_))) :-
    {X =:= 1},
    dump([X], [x], _).
test(target_must_be_list, error(type_error(list(var), foo))) :-
    dump(foo, _, _).

:- end_tests(clpr_projection).

		 /*******************************
		 *         RESIDUALS		*
		 *******************************/

:- begin_tests(clpr_residuals).

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
test(copy_term_projects_slack_away, Gs = [{A+B>=1.0}]) :-
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
test(copy_term_disequation, Gs = [{A+B=\=1.0}]) :-
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
test(pending_optimisation_is_reusable,
     [ true(near(X2, 1.0))
     , true(near(Y2, 1.0))
     ]) :-
    {Y >= 1, Y =< 5},
    minimize(X*Y),
    copy_term(f(X,Y), f(X2,Y2), Gs),
    assertion(Gs = [{_}, clpr:minimize(_)]),
    maplist(call, Gs),
    {X2 =:= 1}.
test(dump_omits_pending_goals, true(C = [y >= _, y =< _])) :-
    {Y >= 1, Y =< 5},
    minimize(_X*Y),
    dump([Y], [y], C).
test(residual_is_reusable, [true(near(I,1.0)), true(near(S,3.0))]) :-
    {X >= 1, X =< 3},
    copy_term(X, Y, Gs),
    maplist(call, Gs),
    inf(Y, I), sup(Y, S).

:- end_tests(clpr_residuals).

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

:- begin_tests(clpr_unify).

test(unify_number_ok) :-
    {X >= 1}, X = 2.
test(unify_number_violates, fail) :-
    {X >= 1}, X = 0.
test(unify_float) :-
    {X >= 0.5}, X = 0.5.
test(unify_integer) :-
    {X >= 1}, X = 1.
test(unify_rational_type_error, error(type_error(real, _))) :-
    R is 1 rdiv 2,
    {X >= 0}, X = R.
test(unify_atom_type_error, error(type_error(real, a))) :-
    {X >= 1}, X = a.
test(unify_two_constrained) :-
    {X >= 1}, {Y =< 0},
    \+ X = Y.
test(unify_two_constrained_ok, [true(near(I,1.0)), true(near(S,3.0))]) :-
    {X >= 1}, {Y =< 3},
    X = Y,
    inf(X, I), sup(X, S).
test(unify_propagates_equation, true(near(X, 0.5))) :-
    {X + Y =:= 1},
    X = Y.
test(clp_type_r, T == clpr) :-
    {X > 1},
    clp_type(X, T).
test(clp_type_unconstrained, fail) :-
    clp_type(_, _).
test(mix_clpr_clpq, error(permission_error(_,_,_))) :-
    {X > 1},
    clpq:{X > 2}.
test(mix_clpr_clpq_unify, error(permission_error(_,_,_))) :-
    {X > 1},
    clpq:{Y > 2},
    X = Y.

test(mix_detected_in_inequality_leq, error(permission_error(_,_,_))) :-
    clpq:{X >= 1},
    {X =< 0}.
test(mix_detected_in_inequality_geq, error(permission_error(_,_,_))) :-
    clpq:{X =< 1},
    {X >= 2}.
test(mix_detected_in_strict_lower, error(permission_error(_,_,_))) :-
    clpq:{X =< 1},
    {X > 2}.
test(mix_detected_in_nonstrict_upper, error(permission_error(_,_,_))) :-
    clpq:{X >= 1},
    {X =< -1}.
test(mix_detected_in_nonstrict_lower, error(permission_error(_,_,_))) :-
    clpq:{X =< 1},
    {X >= 2}.

:- end_tests(clpr_unify).

		 /*******************************
		 *      SOLVER INTERNALS	*
		 *******************************/

:- begin_tests(clpr_internals).

test(fresh_strict_upper, [true(near(S, 0.0)), true(\+ {X =:= 0})]) :-
    {X < 0},
    sup(X, S).
test(fresh_strict_lower, [true(near(I, 0.0)), true(\+ {X =:= 0})]) :-
    {X > 0},
    inf(X, I).
test(fresh_nonstrict_upper, true(near(S, 0.0))) :-
    {X =< 0},
    sup(X, S),
    {X =:= 0}.
test(fresh_nonstrict_lower, true(near(I, 0.0))) :-
    {X >= 0},
    inf(X, I),
    {X =:= 0}.
test(ground_inequality_after_aliasing) :-
    {X =:= Y},
    {X - Y =< 1},
    assertion(\+ {X - Y < 0}),
    {X - Y =< 0}.
test(bound_on_dependent_variable, true(C = [z >= _, z =< _])) :-
    {Z =:= _X + _Y},
    {Z >= 1, Z =< 3},
    dump([Z], [z], C).
test(lower_bound_repair, true(near(I, 3.0))) :-
    {X =< 5, Y =< 5},
    {Z =:= X + Y},
    {Z >= 8},
    inf(X, I).
test(implied_bound_narrowing, true(near(S, 1.0))) :-
    {X >= 0, X =< 10, Y >= 0, Y =< 1, X =< Y},
    sup(X, S).
test(unbounded_culprit, true(near(S, 99.0))) :-
    {X >= 0},
    {Y =:= X + 1},
    {Y =< 100},
    {X =< 200},
    sup(X, S).
test(chained_classes,
     [ true(near(B,1.0))
     , true(near(C,1.0))
     , true(near(D,2.0))
     ]) :-
    {A + B =:= 1, B + C =:= 2, C + D =:= 3},
    {A =:= 0}.
test(simplex_three_variables, true(near(S, 10.0))) :-
    { X >= 0, Y >= 0, Z >= 0,
      X + Y + Z =< 10,
      X + 2*Y =< 8,
      Y + 3*Z =< 9 },
    sup(X + Y + Z, S).
test(strict_slack, [true(near(S, 1.0)), true(\+ {X =:= 1})]) :-
    {X + Y < 1, X > 0, Y > 0},
    sup(X, S).
test(nonzero_with_bound) :-
    {X =\= 0},
    {X >= 0},
    \+ {X =:= 0}.
test(fourier_motzkin_two_sided, true(C = [x >= _, x =< _])) :-
    {X - Y =< 1, Y - X =< 1, Y >= 0, Y =< 10},
    dump([X], [x], C).

% Eliminating a variable adds inequalities that may be redundant, and
% only those are checked for redundancy; x =< 5 is generated from
% x =< y, y =< 5 and is implied by x =< 3.
test(fourier_motzkin_new_row_redundant, true((C = [x =< B], abs(B-3) < 1.0e-9))) :-
    {X =< Y, Y =< 5, X =< 3},
    dump([X], [x], C).
test(fourier_motzkin_longer_chain, true(C = [a-e =< _])) :-
    {A =< B, B =< C0, C0 =< D, D =< E},
    dump([A,E], [a,e], C).
% The variables to eliminate are in two classes.
test(fourier_motzkin_two_classes, true(C = [u >= _, x =< _])) :-
    {X =< Y, Y =< 1, U >= V, V >= 2},
    dump([X,U], [x,u], C).
test(fourier_motzkin_strict, true(C = [x < _])) :-
    {X < Y, Y =< Z, Z < 4},
    dump([X], [x], C).
% Two variables to eliminate, each generating as many inequalities.
test(fourier_motzkin_cycle, true((C = [x >= L, x =< H], abs(L+2) < 1.0e-9, abs(H-12) < 1.0e-9))) :-
    {X - Y =< 1, Y - Z =< 1, Z - X =< 1, Y >= 0, Z =< 10},
    dump([X], [x], C).

% Aliasing variables with different bound types re-posts the bounds of one
% on the other (verify_type_var/5 in itf_r.pl).

test(alias_upper_with_lower, [true(near(I, 0.0)), true(near(S, 5.0))]) :-
    {X =< 5}, {Y >= 0},
    X = Y,
    inf(X, I), sup(X, S).
test(alias_two_intervals, [true(near(I, 2.0)), true(near(S, 5.0))]) :-
    {X >= 1, X =< 5}, {Y >= 2, Y =< 9},
    X = Y,
    inf(X, I), sup(X, S).
test(alias_strict_bounds, [true(\+ {X =:= 1}), true(\+ {X =:= 5})]) :-
    {X > 1}, {Y < 5},
    X = Y.
test(alias_strict_intervals, true(C = [x > _, x < _])) :-
    {X > 1, X < 9}, {Y > 0, Y < 5},
    X = Y,
    dump([X], [x], C).
test(alias_after_pivoting, true(near(I, 2.0))) :-
    {X >= 1, Y >= 1, X + Y =< 4},
    sup(X, _),
    {Z >= 2},
    X = Z,
    inf(X, I).

% Several delayed goals on one variable.

test(two_delayed_goals, [true(near(Y, 3.0)), true(near(Z, 6.0))]) :-
    {X*Y =:= 6},
    {X*Z =:= 12},
    {X =:= 2}.
test(nonlinear_residual_is_reported_once, true(Gs = [{_}])) :-
    {X*Y =:= 6},
    copy_term(X-Y, _, Gs).
test(unrelated_stores_are_reported_separately, true(Gs = [{_},{_}])) :-
    {X*Y =:= 6},
    {A + B =:= 1},
    copy_term(f(X,Y,A,B), _, Gs).
test(alias_across_delayed_goals,
     [ true(near(Y, 3.0))
     , true(near(W, 4.0))
     ]) :-
    {X*Y =:= 6},
    {Z*W =:= 12},
    Y = Z,
    {X =:= 2}.

% Projections leaving active bounds and mixed strictness behind.

test(project_strict_system, true(C = [x < _, x > _])) :-
    {X > 0, Y > 0, X + Y < 10, X - Y > -5},
    dump([X], [x], C).
test(project_with_equality, true(C = [x-y =< _, x+y =< _, x >= _])) :-
    {X >= 0, Y >= 0, Z >= 0, X + Y + Z =:= 1, X =< Y},
    dump([X,Y], [x,y], C).
test(project_mixed_strictness, true(C = [y = _-x, x < _, x >= _])) :-
    {X >= 1, X < 5, Y > 1, Y =< 5, X + Y =:= 4},
    dump([X,Y], [x,y], C).
test(project_after_optimisation, true(C = [y >= _, x+y =< _, x >= _])) :-
    {X >= 1, Y >= 1, X + Y =< 6},
    sup(X + Y, _),
    dump([X,Y], [x,y], C).
test(project_strict_interval, true(C = [y > _, x+y =< _, x > _])) :-
    {X > 0, X < 10, Y > 0, Y < 10, X + Y =< 5},
    dump([X,Y], [x,y], C).

% Ground evaluation of the non-linear functions (nl_eval/2).

test(eval_sin, true(near(X, 0.0))) :-
    {X =:= sin(0)}.
test(eval_cos, true(near(X, 1.0))) :-
    {X =:= cos(0)}.
test(eval_tan, true(near(X, 0.0))) :-
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
test(nonlinear_lt_woken, [true(C = [y < _])]) :-
    {X*Y < 6},
    {X =:= 2},
    dump([Y], [y], C).

% Residual goals for each kind of delayed constraint (transg//1).

test(residual_nonlinear_le, true(C = [_ + y*x =< _])) :-
    {X*Y =< 6},
    dump([X,Y], [x,y], C).
test(residual_nonlinear_lt, true(C = [_ + y*x < _])) :-
    {X*Y < 6},
    dump([X,Y], [x,y], C).
test(residual_nonlinear_ne, true(C = [_ + y*x =\= _])) :-
    {X*Y =\= 6},
    dump([X,Y], [x,y], C).
test(residual_negative_exponent, true(C = [x - _/y = _])) :-
    {X =:= 1/Y},
    dump([X,Y], [x,y], C).
test(residual_nested_function, true(C = [x - sin(_+y) = _])) :-
    {X =:= sin(Y+1)},
    dump([X,Y], [x,y], C).

% Optimisation of an expression that is not yet linear waits.

test(minimize_waits_for_linear,
     [ true(near(X, 1.0))
     , true(near(Y, 1.0))
     ]) :-
    {Y >= 1, Y =< 5},
    minimize(X*Y),
    {X =:= 1}.
test(inf_of_nonlinear_waits, [true(near(I, 1.0))]) :-
    {Y >= 1, Y =< 5},
    inf(X*Y, I),
    {X =:= 1}.

% Division by a non-constant.

test(division_by_expression, [true(near(X, 0.5))]) :-
    {X =:= 1/(Y+1)},
    {Y =:= 1}.

% Wide expressions take the recursive branches of the logarithmic helpers.

test(wide_product, [true(near(Z, 25.0))]) :-
    {Z =:= (A+B+C+D+E)*(A+B+C+D+E)},
    {A =:= 1, B =:= 1, C =:= 1, D =:= 1, E =:= 1}.
test(wide_repair, [true(near(Z, 44.0))]) :-
    {Z =:= A*B + C*D + E*F},
    {A =:= 1, B =:= 2, C =:= 3, D =:= 4, E =:= 5, F =:= 6}.
test(entailed_disequation) :-
    {X =:= 4},
    entailed(X =\= 3).

% --- gaps found by reading the annotated coverage sources ---

test(row_cancellation,
     [ true(near(X, 2.0))
     , true(near(A, 3.0))
     , true(near(B, 1.0))
     ]) :-
    {A =:= X + Y},
    {B =:= X - Y},
    {A + B =:= 4},
    {Y =:= 1}.
test(leading_coefficient_minus_one, C == [y = -x]) :-
    {X + Y =:= 0},
    dump([X,Y], [x,y], C).
test(nonzero_variable_becomes_linear, true(near(Y, 4.0))) :-
    {X =\= 3},
    X = Y,
    {Y + Z =:= 5},
    {Z =:= 1}.
test(mix_detected_in_inequality, error(permission_error(_,_,_))) :-
    clpq:{X >= 1},
    {X < 0}.
test(exponent_cancellation, true(near(Y, 1.0))) :-
    {Y =:= X * (1/X)}.
test(optimisation_redelayed, [true(var(Z))]) :-
    {X*Y*Z >= 1},
    minimize(X*Y*Z),
    {X =:= 1}.

test(residual_leading_coefficient, true(C = [2.0*(x*y) =< _])) :-
    {2*X*Y =< 0},
    dump([X,Y], [x,y], C).
test(residual_leading_negation, true(C = [-(y*x) =< _])) :-
    {-(X*Y) =< 0},
    dump([X,Y], [x,y], C).
test(row_cancellation_in_merge, [true(near(A, 7.0)), true(near(B, -7.0))]) :-
    {A =:= X}, {B =:= 0-X}, {C =:= 0},
    {A + B + C =:= 0},
    assertion(var(X)),
    {X =:= 7}.
test(renormalize_over_bound_variable, true(C = [z = _-y])) :-
    {X + Y + Z =:= 1}, {X =:= 0},
    ordering([Z,Y]),
    dump([Y,Z], [y,z], C).

:- end_tests(clpr_internals).

		 /*******************************
		 *          EXAMPLES		*
		 *******************************/

:- begin_tests(clpr_examples).

% The mortgage relation from the OFAI manual / the Monash examples.

mg(P, T, I, B, MP) :-
    {T = 1, B + MP =:= P * (1 + I)}.
mg(P, T, I, B, MP) :-
    {T > 1, P1 =:= P*(1+I) - MP, T1 =:= T - 1},
    mg(P1, T1, I, B, MP).

test(mortgage_forward, true(near(B, 7.0))) :-
    mg(1000, 3, 0.1, B, 400),
    !.
test(mortgage_backward, true(near(P, 1324000/1331))) :-
    mg(P, 3, 0.1, 0, 400),
    !.
test(mortgage_relation, true(C = [b = _*p - _*mp])) :-
    mg(P, 3, 0.1, B, MP),
    !,
    dump([P,B,MP], [p,b,mp], C).

% Fibonacci, forwards and backwards.  Note that the base cases must be
% written as constraints: CLP(R) binds its variables to *floats*, so a
% clause head fib(0,0) would not unify with the 0.0 the solver produces.

fib(N, F) :- {N =:= 0, F =:= 0}.
fib(N, F) :- {N =:= 1, F =:= 1}.
fib(N, F) :-
    {N > 1, N1 =:= N-1, N2 =:= N-2, F =:= F1 + F2},
    fib(N1, F1),
    fib(N2, F2).

test(fib_forward, true(near(F, 55.0))) :-
    fib(10, F), !.
test(fib_backward, true(near(N, 10.0))) :-
    fib(N, 55.0), !.
test(fib_integer_head_does_not_unify, fail) :-
    % the reason for the base cases above
    int_fib(10, _).

int_fib(0, 0).
int_fib(1, 1).
int_fib(N, F) :-
    {N > 1, N1 =:= N-1, N2 =:= N-2, F =:= F1 + F2},
    int_fib(N1, F1),
    int_fib(N2, F2).

test(convex_combination, [true(near(Min, 1.0)), true(near(Max, 9.0))]) :-
    { A >= 0, B >= 0, C >= 0,
      A + B + C =:= 1,
      X =:= 1*A + 4*B + 9*C },
    inf(X, Min), sup(X, Max).

% The "Variable Ordering" section of OFAI TR-95-09 works these examples
% with the 12 period mortgage.  They are reproduced here verbatim; note
% that assertion/1 does not keep bindings, so the shape is matched with
% plain unification and only the coefficients are asserted.

test(ordering_manual_plain,
     [ true(near(Cp, 1.1268250301319698))
     , true(near(Cm, 12.682503013196973))
     ]) :-
    % {B=1.1268250301319698*P-12.682503013196973*Mp}
    mg(P, 12, 0.01, B, Mp), !,
    dump([P,B,Mp], [p,b,mp], C),
    C = [b = Cp*p - Cm*mp].
test(ordering_manual_mp,
     [ true(near(Cb, -0.0788487886783417))
     , true(near(Cp, 0.08884878867834171))
     ]) :-
    % "instead of B, you want Mp to be the defined variable":
    % {Mp= -0.0788487886783417*B+0.08884878867834171*P}
    mg(P, 12, 0.01, B, Mp), !,
    ordering([Mp]),
    dump([P,B,Mp], [p,b,mp], C),
    C = [mp = Cb*b + Cp*p].
test(ordering_manual_mp_p,
     [ true(near(Cp, 0.08884878867834171))
     , true(near(Cb, 0.0788487886783417))
     ]) :-
    % "require P to appear before (to the left of) B in an addition":
    % {Mp=0.08884878867834171*P-0.0788487886783417*B}
    mg(P, 12, 0.01, B, Mp), !,
    ordering([Mp,P]),
    dump([P,B,Mp], [p,b,mp], C),
    C = [mp = Cp*p - Cb*b].
test(ordering_manual_before_constraints,
     [ true(near(Cm, -12.682503013196973))
     , true(near(Cp, 1.1268250301319698))
     ]) :-
    % "ordering/1 acts like a constraint: you can put it anywhere in the
    % computation": {B= -12.682503013196973*Mp+1.1268250301319698*P}
    ordering(B < Mp),
    mg(P, 12, 0.01, B, Mp), !,
    dump([P,B,Mp], [p,b,mp], C),
    C = [b = Cm*mp + Cp*p].

% Newton's method for sqrt(2), from the OFAI manual's precision section.

newton(X, X0, X1) :-
    {X1 =:= X0 - (X0*X0 - X)/(2*X0)}.

test(newton_sqrt2, true(near(E, 1.4142135623730951))) :-
    newton(2, 1.0, A),
    newton(2, A, B),
    newton(2, B, C),
    newton(2, C, D),
    newton(2, D, E).

:- end_tests(clpr_examples).

		 /*******************************
		 *      TOPLEVEL PRINTING	*
		 *******************************/

% The residual constraints the toplevel prints for a query come from
% clpr.pl's own prolog:message//1 hook rather than from attribute_goals//1.

:- begin_tests(clpr_toplevel).

test(bounds, true(near(B, 3.0))) :-
    {X > 3},
    clpr:dump_toplevel_bindings(['X'=X], C),
    C = ['X' > B].
test(equation, true(C = ['Y' = _-'X'])) :-
    {X + Y =:= 1},
    clpr:dump_toplevel_bindings(['X'=X,'Y'=Y], C).
test(nonlinear, true(C = [_ + 'Y'*'X' = _])) :-
    {X*Y =:= 6},
    clpr:dump_toplevel_bindings(['X'=X,'Y'=Y], C).
test(same_variable_reported_once, true(near(B, 3.0))) :-
    % a variable bound to two names must be dumped only once
    {X > 3},
    clpr:dump_toplevel_bindings(['A'=X,'B'=X], C),
    C = ['A' > B].
test(unconstrained, C == []) :-
    clpr:dump_toplevel_bindings(['X'=_], C).
test(nonvar_binding, C == []) :-
    clpr:dump_toplevel_bindings(['X'=foo], C).

:- end_tests(clpr_toplevel).

		 /*******************************
		 *        KNOWN ISSUES		*
		 *******************************/

:- begin_tests(clpr_known_issues).

% See doc/design.md, section 14.

test(division_by_zero_does_not_raise, fail) :-
    {_ =:= 1/0}.

:- end_tests(clpr_known_issues).
