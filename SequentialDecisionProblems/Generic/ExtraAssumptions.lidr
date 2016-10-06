> module SequentialDecisionProblems.Generic.ExtraAssumptions

> import SequentialDecisionProblems.Generic.CoreAssumptions

> %default total
> %access public export
> %auto_implicits on

> %hide Prelude.Nat.LTE

* Preliminaries

In order to implememt the full theory of sequential decision problems
presented in |FullTheory|, the core assumptions introduced in
|CoreAssumptions| have to be extended. Here, we present such extension.
As in |CoreAssumptions|, the extra assumptions are implemented as holes.


* |LTE|

In order to show that empty policy sequences are optimal and to
implement Bellman's principle of optimality (please, see
|FullTheory.Bellman|), the binary relation introduced in
|CoreAssumptions| for comparing values of sequences of policies has to
be a preorder

> reflexiveLTE : (a : Val) -> a `LTE` a
> transitiveLTE : (a : Val) -> (b : Val) -> (c : Val) -> a `LTE` b -> b `LTE` c -> a `LTE` c

Also, a proof of |Bellman| requires |plus| and |LTE| to satisfy the
monotonicity condition

> monotonePlusLTE : a `LTE` b -> c `LTE` d -> (a `plus` c) `LTE` (b `plus` d)


* |meas|

Again for implemementing Bellman's optimality principle, the function
|meas| introduced in |CoreAssumption| to describe how a decision maker
measures the possible rewards entailed by (lists, probability
distributions, etc. of) possible next states is required to fulfill a
monotonicity condition

> measMon  :  {A : Type} ->
>             (f : A -> Val) -> (g : A -> Val) ->
>             ((a : A) -> (f a) `LTE` (g a)) ->
>             (ma : M A) -> meas (fmap f ma) `LTE` meas (fmap g ma)

In a nutshell, |measMon| says that, if |ma| and |mb| are similar
|M|-structures and |ma| is smaller or equal to |mb|, than it cannot be
the case that the measure of |ma| is greater than the measure of |mb|.

This conditions was originally formalized by Ionescu in [2] to give a
consistent meaning to harm measures in vulnerability studies.


* |argmax|, |max|

Finally, if |argmax| and |max| fulfill the specification

< argmaxSpec  :  (x : State t) -> (v : Viable (S n) x) ->
<                (f : GoodCtrl t x n -> Val) ->
<                max x v f = f (argmax x v f)

< maxSpec     :  (x : State t) -> (v : Viable (S n) x) ->
<                (f : GoodCtrl t x n -> Val) -> (y : GoodCtrl t x n) ->
<                (f y) `LTE` (max x v f)

then it is easy to show that |optExt| as defined in |CoreTheory| does in
fact compute optimal extensions of arbitrary policy sequences. This and
Bellman's principle of optimality are the key results needed to prove
that |CoreTheory.backwardsInduction| does indeed return optimal policy
sequences, see |FullTheory.backwardsInductionLemma|.


[1] Bellman, Richard; "Dynamic Programming", Princeton University Press,
    1957

[2] Ionescu, Cezar; "Vulnerability Modelling and Monadic Dynamical
    Systems", Freie Universitaet Berlin, 2009
