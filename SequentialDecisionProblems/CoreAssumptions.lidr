> module SequentialDecisionProblems.CoreAssumptions

> import Sigma.Sigma

> %default total
> %access public export
> %auto_implicits off


* Preliminaries

In this module we list the assumptions underlying the core theory of
sequential decision problems presented in |CoreTheory|.

In a nutshell, the core theory introduces the notion of policy, policy
sequence, optimality of policy sequences and implements a generic
backwards induction algorithm |backwardsInduction| for computing optimal
policy sequences.

However, the core theory does not implement a machine checkable proof
that |backwardsInduction| is correct that is, that its result is an
optimal policy sequence.

This is done in the full theory presented in |FullTheory|. The
additional assumptions needed to implement the full theory are
summarized in |FullAssumptions|.

Both here and in |FullAssumptions|, the assumptions are implemented as
holes (metavariables, forward declarations, partial definitions,
etc.). The idea is that users that wish to apply the theory (typically,
for computing optimal solutions for a specific decision problem) will
fill-in the holes by providing problem-specific implementations.


* Sequential decision processes

A sequential decision problem (SDP) is specified in terms of, among
others, its underlying decision process.

In a decision process, a decision maker is required to perform a number
of decision steps. At each step, the decision maker is in (observes) a
state and is required to select a control (action, option). The idea is
that, upon selecting a control in a given state, the decision maker will
enter (observe) a new state. In a deterministic decision process, such
new state is uniquely defined in terms of the current decision step,
state and selected control. But in decision processes under uncertainty,
the decision maker only knows which new states are "possible" (again,
for a given decision step, "current" state and selected control) and,
perhaps, their probabilities. But it does not know which one will
actually occur.

Thus, in order to specify a decision process, one has to first specify
what are the possible states at each decision step:

> State : (t : Nat) -> Type

Then, one has to explain which controls can be selected at a given step
and for a given state:

> Ctrl : (t : Nat) -> (x : State t) -> Type

Finally, one has to explain which "next" states are possible at a given
decision step, in a given state and for a selected control. In the
deterministic case, one could provide such explanation by defining a
stepping function

< step : (t : Nat) -> (x : State t) -> (y : Ctrl t x) -> State (S t)

But what if the decision process has uncertain outcomes? In this case,
we follow an approach originally proposed by Ionescu [1] and generalize
|step| to a monadic transition function:

> M : Type -> Type

> step    : (t : Nat) -> (x : State t) -> (y : Ctrl t x) -> M (State (S t))

For reasons that will become clear in |CoreTheory|, |M| is is required
to be a functor:

> fmap : {A, B : Type} -> (A -> B) -> M A -> M B
> postulate functorSpec1 : fmap . id = id
> postulate functorSpec2 : {A, B, C : Type} -> {f : B -> C} -> {g : A -> B} ->
>                          fmap (f . g) = (fmap f) . (fmap g)

In the above specification and throughout this file, we use postulates
to denote assumtions that we consider to be conceptually relevant but
that are not necessary for teh theory. Thus, strictly speaking, |M| is
not required to be a functor, just to implement |fmap|.

In specific decision processes, we expect |M| to be |Id| (deterministic
SDP), |List| (non-deterministic SDP) or |Prob| (stochastic SDP). But our
assumptions are general enough to specify other kinds of decision
processes.


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
defines a sequential decision problem. But whenever a decision step has
an uncertain outcome, uncertainties about "next" states naturally yield
uncertainties about rewards. In these cases, the decision makes faces a
number of possible rewards (one for each possible next state) and has to
explain how it measures such chances. In stochastic decision problems,
possible next states (and, therefore possible rewards) are labelled with
probabilities. In these cases, possible rewards are often measured in
terms of their expected value.  Here, again, we follow the approach
proposed by Ionescu in [1] and introduce a measure

> meas : M Val -> Val

that characterizes how the decision maker values uncertainties about
rewards in a single decision step. It is possible that a decision maker
values uncertainties according to different measures at different
decision steps. This could be easily formalized by generalising

< meas : M Val -> Val

to

< meas : (t : Nat) -> (x : State t) -> (M Val -> Val)


* Solving sequential decision problems

Implementing the above holes defines a specific SDP unambiguously. But
in order to compute controls that maximize the sum of the rewards over
an arbitrary number of decision steps, we need to be able to assess that
all "next" states in an |M|-structure satisfy certain properties. This
requires |M| to be a "container":

> Elem     : {A : Type} -> A -> M A -> Type
> NotEmpty : {A : Type} -> M A -> Type
> All      : {A : Type} -> (P : A -> Type) -> M A -> Type
> tagElem  : {A : Type} -> (ma : M A) -> M (Sigma A (\ a => a `Elem` ma))

> allElemSpec0 : {A : Type} -> {P : A -> Type} ->
>                (a : A) -> (ma : M A) -> All P ma -> a `Elem` ma -> P a

> postulate elemNotEmptySpec0 : {A : Type} ->
>                               (a : A) -> (ma : M A) ->
>                               a `Elem` ma -> CoreAssumptions.NotEmpty ma

> postulate elemNotEmptySpec1 : {A : Type} ->
>                               (ma : M A) -> CoreAssumptions.NotEmpty ma ->
>                               Sigma A (\ a => a `Elem` ma)

The theory presented in "CoreTheory.lidr" relies on two
further assumptions. Expressing these assumptions requires introducing
the notion of viability.

Intuitively, a state |x : State t| is viable for |n| steps if, in spite
of the uncertainties of the decision process, one can make |n| decision
steps starting from |x| without bumping into a dead end. Here, dead ends
are states for which no controls are available. In concrete decision
problems, they could represent exceptional outcomes: aborting a
computation, running out of fuel, being shot dead.

> Viable : {t : Nat} -> (n : Nat) -> State t -> Type

> Good : (t : Nat) -> (x : State t) -> (n : Nat) -> (Ctrl t x) -> Type
> Good t x n y = (NotEmpty (step t x y), All (Viable {t = S t} n) (step t x y))

> GoodCtrl : (t : Nat) -> (x : State t) -> (n : Nat) -> Type
> GoodCtrl t x n = Sigma (Ctrl t x) (Good t x n)

> postulate viableSpec0 : {t : Nat} ->
>                         (x : State t) -> Viable Z x

> viableSpec1 : {t : Nat} -> {n : Nat} ->
>               (x : State t) -> Viable (S n) x -> GoodCtrl t x n

> postulate viableSpec2 : {t : Nat} -> {n : Nat} ->
>                         (x : State t) -> GoodCtrl t x n -> Viable (S n) x

With viability in place , we are now ready to express the last two
assumption at the core of the theory. In "CoreTheory.lidr" we are going
to implement a generic form (for all |State : (t : Nat) -> Type|, |Ctrl
: (t : Nat) -> (x : State t) -> Type|, |M : Type -> Type|, etc.) of the
backwards induction algorithm originally proposed by Bellman in 1957
[2].

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
