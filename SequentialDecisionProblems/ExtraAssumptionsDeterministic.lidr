> module SequentialDecisionProblems.ExtraAssumptionsDeterministic

> import SequentialDecisionProblems.CoreAssumptionsDeterministic

> %default total
> %access public export
> %auto_implicits off


* Preliminaries

In order to implememt the full theory of sequential decision problems
presented in |FullTheoryDeterministic|, the core assumptions introduced
in |CoreAssumptionsDeterministic| have to be extended. Here, we present
such extension.  As in |CoreAssumptionsDeterministic|, the extra
assumptions are implemented as holes.


* |LTE|

In order to show that empty policy sequences are optimal and to
implement Bellman's principle of optimality (please, see
|FullTheoryDeterministic.Bellman|), the binary relation introduced in
|CoreAssumptionsDeterministic| for comparing values of sequences of
policies has to be a preorder

> reflexiveLTE : (a : Val) -> a `LTE` a
> transitiveLTE : (a : Val) -> (b : Val) -> (c : Val) -> a `LTE` b -> b `LTE` c -> a `LTE` c

Also, a proof of |Bellman| requires |plus| and |LTE| to satisfy the
monotonicity condition

> monotonePlusLTE : {a, b, c, d  : Val} -> a `LTE` b -> c `LTE` d -> (a `plus` c) `LTE` (b `plus` d)


* |argmax|, |max|

Finally, if |argmax| and |max| fulfill the specification

> argmaxSpec : {t : Nat} -> {n : Nat} ->
>              (x : State t) -> (v : Viable (S n) x) ->
>              (f : GoodCtrl t x n -> Val) ->
>              max x v f = f (argmax x v f)

> maxSpec : {t : Nat} -> {n : Nat} ->
>           (x : State t) -> (v : Viable (S n) x) ->
>           (f : GoodCtrl t x n -> Val) -> (y : GoodCtrl t x n) ->
>           (f y) `LTE` (max x v f)

then it is easy to show that |optExt| as defined in
|CoreTheoryDeterministic| does in fact compute optimal extensions of
arbitrary policy sequences. This and Bellman's principle of optimality
are the key results needed to prove that
|CoreTheoryDeterministic.backwardsInduction| does indeed return optimal
policy sequences, see |FullTheoryDetrministic.backwardsInductionLemma|.


[1] Bellman, Richard; "Dynamic Programming", Princeton University Press,
    1957

[2] Ionescu, Cezar; "Vulnerability Modelling and Monadic Dynamical
    Systems", Freie Universitaet Berlin, 2009
