> module SequentialDecisionProblems.Deterministic.CoreAssumptions

> import Sigma.Sigma

> %default total
> %access public export
> %auto_implicits on


* Preliminaries

In this module we list the assumptions underlying the core theory of
sequential decision problems presented in |CoreTheoryDeterministic|.

In a nutshell, the core theory introduces the notion of policy, policy
sequence, optimality of policy sequences and implements a generic
backwards induction algorithm |backwardsInduction| for computing optimal
policy sequences.

However, the core theory does not implement a machine checkable proof
that |backwardsInduction| is correct that is, that its result is an
optimal policy sequence.

This is done in the full theory presented in
|FullTheoryDeterministic|. The additional assumptions needed to
implement the full theory are summarized in
|ExtraAssumptionsDeterministic|.

Both here and in |ExtraAssumptionsDeterministic|, the assumptions are
implemented as holes (metavariables, forward declarations, partial
definitions, etc.). The idea is that users that wish to apply the theory
(typically, for computing optimal solutions for a specific decision
problem) will fill-in the holes by providing problem-specific
implementations.


* Sequential decision processes
 
A sequential decision problem (SDP) is specified in terms of, among
others, its underlying decision process.

In a decision process, a decision maker is required to perform a number
of decision steps. At each step, the decision maker is in (observes) a
state and is required to select a control (action, option). The idea is
that, upon selecting a control in a given state, the decision maker will
enter (observe) a new state. In a deterministic decision process, such
new state is uniquely defined in terms of the current decision step,
state and selected control.

Thus, in order to specify a decision process, one has to first specify
what are the possible states at each decision step:

> State : (t : Nat) -> Type

Then, one has to explain which controls can be selected at a given step
and for a given state:

> Ctrl : (t : Nat) -> (x : State t) -> Type

Finally, one has to explain which "next" state is obtained at a given
decision step, in a given state and for a selected control:

> next : (t : Nat) -> (x : State t) -> (y : Ctrl t x) -> State (S t)


* Sequential decision problems

In order to obtain a problem from a decision process, we introduce the
additional assumption that, with each transition from the current state
to a new state, the decision maker receives a certain reward (payoff,
etc.)

> Val : Type

> reward  : (t : Nat) -> (x : State t) -> (y : Ctrl t x) -> (x' : State (S t)) -> Val

Since the original work of Bellman [1957], this has turned out to be a
useful abstraction. The idea is that the decision maker seeks controls
that maximize the sum of the rewards obtained in a decision
process. Thus, values of type |Val| have to be "addable"

> plus : Val -> Val -> Val

We will also need |Val| to be equipped with a "zero"

> zero : Val

and with a binary "comparison" relation

> LTE : Val -> Val -> Type

In a deterministic case, implementing the above assumptions completely
defines a sequential decision problem. 


* Solving sequential decision problems

Implementing the above holes defines a specific SDP unambiguously. The
theory presented in |CoreTheoryDeterministic| supports computing
controls that maximize the sum of the rewards over an arbitrary number
of decision steps. But expressing the theory requires introducing the
notion of viability.

Intuitively, a state |x : State t| is viable for |n| steps if one can
make |n| decision steps starting from |x| without bumping into a dead
end. Here, dead ends are states for which no controls are available. In
concrete decision problems, they could represent exceptional outcomes:
aborting a computation, running out of fuel, being shot dead.

> Viable : (n : Nat) -> State t -> Type

> Good : (t : Nat) -> (x : State t) -> (n : Nat) -> (Ctrl t x) -> Type
> Good t x n y = Viable {t = S t} n (next t x y)

> GoodCtrl : (t : Nat) -> (x : State t) -> (n : Nat) -> Type
> GoodCtrl t x n = Sigma (Ctrl t x) (Good t x n)

> postulate viableSpec0 : (x : State t) -> Viable Z x

> viableSpec1 : (x : State t) -> Viable (S n) x -> GoodCtrl t x n

> postulate viableSpec2 : (x : State t) -> GoodCtrl t x n -> Viable (S n) x

With viability in place , we are now ready to express the last two
assumption of |CoreTheoryDeterministic|. There, we are going to
implement a generic form (for all |State : (t : Nat) -> Type|, |Ctrl :
(t : Nat) -> (x : State t) -> Type|, etc.) of the backwards induction
algorithm originally proposed by Bellman in 1957 [2].

The algorithm essentially relies on being able to compute, for each
possible state at a given decision step |x : State t| a control in |Ctrl
t x| that maximises an arbitrary function from |Ctrl t x| to |Nat|. As
it turns out, we can relax a little bit this assumption and only require
to be able to compute such "optimal" controls only for those states in
|State t| which are viable for a certain number of steps. Thus, we
assume that users that want to apply the theory are able to implement
two functions

> argmax : {t : Nat} -> {n : Nat} ->
>          (x : State t) -> (Viable (S n) x) ->
>          (f : GoodCtrl t x n -> Val) -> GoodCtrl t x n

> max    : {t : Nat} -> {n : Nat} ->
>          (x : State t) -> (Viable (S n) x) ->
>          (f : GoodCtrl t x n -> Val) -> Val

The idea is that |argmax| and |max| fulfill the specification

< argmaxSpec : {t : Nat} -> {n : Nat} ->
<              (x : State t) -> (v : Viable (S n) x) ->
<              (f : GoodCtrl t x n -> Val) ->
<              max x v f = f (argmax x v f)

< maxSpec : {t : Nat} -> {n : Nat} ->
<           (x : State t) -> (v : Viable (S n) x) ->
<           (f : GoodCtrl t x n -> Val) -> (y : GoodCtrl t x n) ->
<           (f y) `LTE` (max x v f)

As it turns out, |argmaxSpec| and |maxSpec| are only needed to implement
the full theory. We introduced them explicitly in |FullAssumptions|.


* References

[1] Bellman, Richard; "Dynamic Programming", Princeton University Press,
    1957

[2] Ionescu, Cezar; "Vulnerability Modelling and Monadic Dynamical
    Systems", Freie Universitaet Berlin, 2009
