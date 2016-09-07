> module SequentialDecisionProblems.Generic.CoreNaiveTheory

> import SequentialDecisionProblems.Generic.CoreNaiveAssumptions

> import Sigma.Sigma

> %default total
> %access public export
> %auto_implicits on


* The core theory of monadic sequential decision problems (SDP):

** Policies and policy sequences

Policies are just functions that associate to every state |x| at
decision step |t| which is reachable and viable for |S m| steps (from
which |S m| more decision steps are doable) a "good" control, see
"SeqDecProbsCoreAssumptions":

> Policy    :  (t : Nat) -> Type
> Policy t  =  (x : State t) -> Ctrl t x

A policy sequence for making |n| decision steps starting from some
(reachable, viable for |n| steps) state at decision step |t| is just a
list of policies of length |n|, one for each decision step:

> data PolicySeq : (t : Nat) -> (n : Nat) -> Type where
>   Nil   :  PolicySeq t Z
>   (::)  :  Policy t -> PolicySeq (S t) n -> PolicySeq t (S n)


** The value of policy sequences

As mentioned in |CoreAssumptions|, the idea of a decision problem is
that the decision maker seeks controls that maximize the sum of the
rewards obtained in a decision process. 

Thus, in order to meaningfully define a notion of optimality for policy
sequences, we have to compute the value (in terms of possible sums of
rewards) of making decisions according to a given policy sequence.

Specifically, for a policy sequence |ps : PolicySeq tn| and a state |x :
State t|, we have to compute the value (in terms of possible sums of
rewards) of making |n| decision steps with |ps| starting from |x|:

<   val : (x : State t) -> PolicySeq t n -> Val

The case |n = Z| (and |ps = Nil|) is trivial. Here, we are not making
any decision step. Thus, we do not collect any reward and the value is
just zero:

<   val {t} {n = Z} x Nil = zero

If |n = S m| and |ps| consists of a policy |p : Policy t (S m)| and of a
policy sequence |ps : PolicySeq (S t) m|, things are slightly more
complicated:

<   val {t} {n = S m} x (p :: ps) = ?

Here, we first have to compute the rewards obtained by selecting the
control |y = p x| in the first decision step. We get one possible reward
for each state in |nexts t x y|. Thus, if |x' `Elem` (nexts t x y)|, its
corresponding reward is

< reward t x y x'

Next, we have to add to all these rewards (one for every |x'|) the
values of making |m| further decision steps with |ps| starting from
|x'|:

< val x' ps

Finally, we have to reduce all possible values to a single aggregated
value. Here is where the measure |meas| comes into place. Thus, the full
implementation is simple

> val : (x : State t) -> PolicySeq t n -> Val
> val {t} {n = Z} x ps = zero
> val {t} {n = S m} x (p :: ps) = meas (fmap f mx') where
>   y    :  Ctrl t x
>   y    =  p x
>   f    :  State (S t) -> Val
>   f x' =  reward t x y x' `plus` val x' ps 
>   mx'  :  M (State (S t))
>   mx'  =  nexts t x y

Notice that in the computation we have used, among others, the following
assumtions from |CoreAssumtions|:


**  Optimality of policy sequences:

With a function for computing the value (in terms of "possible" sums of
rewards) of making |n| decision steps with a policy sequence starting
from some specific state, we can easily put forward what it means for
one such sequences to be optimal.

Informally, we say that a policy sequence |ps| for making |n| decision
steps starting from states in |State t| which are reachable and viable
for |n| steps is optimal if it value is at least as good as the value of
any other policy sequence for making |n| decision steps starting from
states in |State t|. Formally:

> |||
> OptPolicySeq : PolicySeq t n -> Type
> OptPolicySeq {t} {n} ps  =  (ps' : PolicySeq t n) ->
>                             (x : State t) ->
>                             (val x ps') `LTE` (val x ps)

Notice that the above notion of optimality is very strong. It entails a
quantification over all states of |State t| to which the first policy of
the sequence can be applied.

Thus, if we manage to compute an optimal policy sequence of length |n|
for making |n| decisions starting from step |t|, we have the guarantee
that, no matter which state we will happen to be at decision step |t|,
there is no better way to make |n| decision steps than that encoded by
our policy.

In other words, we have |n| rules for making "best" (in terms of
"possible" sums of rewards) decisions.

Thus, an obvious question is whether it is at all possible to compute
sequences of policies that are optimal in the above sense. As we shall
see in |FullNaiveTheory|, if the assumptions put forward in
|FullNaiveAssumptions| are fulfilled, the answer to this question is
positive.

In the rest of this file, we implement a generic backwards induction
algorithm for computing optimal policy sequences for an arbitrary number
of decision steps.


** Optimal extensions of policy sequences:

The computation at the core of backwards induction is the computation of
an optimal extension of a policy sequence. An extension of a policy
sequence for making |m| decision steps starting from states at decision
step |S t| is just a policy for taking decisions at step |t|. 

Informally, a policy |p| is an "optimal" extension of a policy sequence
|ps| if there is no better way than |p :: ps| to make |S m| decision
steps at step |t|. Formally:

> |||
> OptExt : PolicySeq (S t) m -> Policy t -> Type
> OptExt {t} ps p  =  (p' : Policy t) -> (x : State t) ->
>                     (val x (p' :: ps)) `LTE` (val x (p :: ps))

The idea behind the notion of optimal extension is that if |p| is an
optimal extension of |ps| and |ps| is optimal, then |p :: ps| is optimal.

This is Bellman's principle of optimality [1] which we will implement in
|FullNaiveTheory|. There, we will also show that, under the assumptions
put forward in |FullNaiveAssumptions|,

> ||| 
> cval : (x  : State t) -> (ps : PolicySeq (S t) n) -> Ctrl t x -> Val
> cval {t} {n} x ps y = meas (fmap f mx') where
>   f    :  State (S t) -> Val
>   f x' =  reward t x y x' `plus` val x' ps 
>   mx'  :  M (State (S t))
>   mx'  =  nexts t x y

> ||| 
> optExt : PolicySeq (S t) n -> Policy t
> optExt {t} ps = p where
>   p : Policy t
>   p x = argmax x (cval x ps)

does in fact compute optimal extensions of arbitrary policy sequences.


** Generic machine checkable backwards induction

If |LTE| is reflexive, it is straightforward to show that empty policy
sequences (that is, sequences for performing zero decision steps) are
optimal. 

This observation and the formulation of Bellman's principle of
optimality mentioned above (optimal extensions of optimal policy
sequences are optimal), suggest the following implementations of
backwards induction:

> backwardsInduction : (t : Nat) -> (n : Nat) -> PolicySeq t n
> backwardsInduction t  Z     =  Nil
> backwardsInduction t (S n)  =  optExt ps :: ps where
>   ps : PolicySeq (S t) n
>   ps = backwardsInduction (S t) n

In |FullTheory| we will show that, under the additional assumptions
listed in |FullAssumptions|, |backwardsInduction| computes provably
optimal sequences of policies for arbitrary SDPs and number of decision
steps.


[1] Bellman, Richard; "Dynamic Programming", Princeton University Press,
    1957


> {-

> ---}


