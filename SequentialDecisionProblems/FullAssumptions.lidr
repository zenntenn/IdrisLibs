> module SequentialDecisionProblems.FullAssumptions

> import SequentialDecisionProblems.CoreAssumptions

> import Sigma.Sigma
> import Sigma.Operations

> %default total
> %access public export
> %auto_implicits off


* Preliminaries

In this module we add to |CoreAssumptions| the assumptions required to
implement the full theory of sequential decision problems presented in
|FullTheory|.

As in |CoreAssumptions|, the assumptions are implemented as holes
(metavariables, forward declarations, partial definitions, etc.). The
idea is that users that wish to apply the theory (typically, for
computing provably optimal solutions for a specific decision problem)
will fill-in the holes by providing problem-specific implementations.


* |LTE|

The binary relation introduced in |CoreAssumptions| for comparing values
of sequences of policies is required to be a preorder

> reflexiveLTE : (a : Val) -> a `LTE` a
> transitiveLTE : (a : Val) -> (b : Val) -> (c : Val) -> a `LTE` b -> b `LTE` c -> a `LTE` c

and to satisfy the monotonicity condition

> monotonePlusLTE : {a, b, c, d  : Val} -> a `LTE` b -> c `LTE` d -> (a `plus` c) `LTE` (b `plus` d)


* |meas|

The function |meas| introduced in |CoreAssumption| to describe how a
decision maker measures the possible rewards entailed by (lists,
probability distributions, etc. of) possible next states is required to
fulfill a monotonicity condition

> measMon  :  {A : Type} ->
>             (f : A -> Val) -> (g : A -> Val) ->
>             ((a : A) -> (f a) `LTE` (g a)) ->
>             (ma : M A) -> (meas (fmap f ma)) `LTE` (meas (fmap g ma))

In a nutshell, |measMon| says that, if |ma| and |mb| are similar
|M|-structures and |ma| is smaller or equal to |mb|, than it cannot be
the case that the measure of |ma| is greater than the measure of |mb|.

This conditions was originally formalized by Ionescu in [2] to give a
consustent meaning to harm measures in vulnerability studies.


* ...

> maxSpec : {t : Nat} -> {n : Nat} ->
>           (x : State t) -> (v : Viable (S n) x) ->
>           (f : GoodCtrl t x n -> Val) -> (y : GoodCtrl t x n) ->
>           (f y) `LTE` (max x v f)

> argmaxSpec : {t : Nat} -> {n : Nat} ->
>              (x : State t) -> (v : Viable (S n) x) ->
>              (f : GoodCtrl t x n -> Val) ->
>              max x v f = f (argmax x v f)

[1] Bellman, Richard; "Dynamic Programming", Princeton University Press,
    1957

[2] Ionescu, Cezar; "Vulnerability Modelling and Monadic Dynamical
    Systems", Freie Universitaet Berlin, 2009
