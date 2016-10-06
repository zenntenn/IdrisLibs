> module SequentialDecisionProblems.Generic.CoreTheory

> import SequentialDecisionProblems.Generic.CoreAssumptions

> import Sigma.Sigma

> %default total
> %access public export
> %auto_implicits on


* Auxiliary functions

> |||
> ctrl : GoodCtrl t x n -> Ctrl t x
> ctrl (MkSigma y _) = y

> |||
> good : (y : GoodCtrl t x n) -> Good t x n (ctrl y)
> good (MkSigma _ p) = p

> |||
> allViable : (y : GoodCtrl t x n) -> All (Viable n) (nexts t x (ctrl y)) 
> allViable (MkSigma _ p) = snd p


* The core theory of monadic sequential decision problems (SDP):


** Reachability

In |CoreAssumptions|, we have introduced the notion of viability. This
is, strictly speaking, all what is needed to formalize the notion of
policies as functions that associate "good" controls to viable states.

But in a decision problem, not all viable states are actually
reachable. Thus, we would like to further restrict the domain of
policies to states that can actually be reached. Intuitively, a state is
reachable if there are controls that allow for a path from some initial
state to that state. Thus, tautologically, every initial state is
reachable:

> Reachable : State t' -> Type

> postulate reachableSpec0 : (x : State Z) -> Reachable x

Moreover, if |x| is reachable and admits a control |y|, then all states
that can be obtained by selecting |y| in |x| are also reachable ...

> reachableSpec1  :  (x : State t) -> Reachable x -> (y : Ctrl t x) -> All Reachable (nexts t x y)

... and the other way round:

> Pred : State t -> State (S t) -> Type
> Pred {t} x x'  =  Sigma (Ctrl t x) (\ y => x' `Elem` nexts t x y)

> ReachablePred : State t -> State (S t) -> Type
> ReachablePred x x'  = (Reachable x, x `Pred` x')

> postulate reachableSpec2  :  (x' : State (S t)) -> Reachable x' -> Sigma (State t) (\ x => x `ReachablePred` x')


** Policies and policy sequences

Policies are just functions that associate to every state |x| at
decision step |t| which is reachable and viable for |S m| steps (from
which |S m| more decision steps are doable) a "good" control, see
"SeqDecProbsCoreAssumptions":

> Policy : (t : Nat) -> (n : Nat) -> Type
> Policy t Z      =  Unit
> Policy t (S m)  =  (x : State t) -> Reachable x -> Viable (S m) x -> GoodCtrl t x m

A policy sequence for making |n| decision steps starting from some
(reachable, viable for |n| steps) state at decision step |t| is just a
list of policies of length |n|, one for each decision step:

> data PolicySeq : (t : Nat) -> (n : Nat) -> Type where
>   Nil   :  PolicySeq t Z
>   (::)  :  Policy t (S n) -> PolicySeq (S t) n -> PolicySeq t (S n)


** The value of policy sequences

As mentioned in |CoreAssumptions|, the idea of a decision problem is
that the decision maker seeks controls that maximize the sum of the
rewards obtained in a decision process. 

Thus, in order to meaningfully define a notion of optimality for policy
sequences, we have to compute the value (in terms of possible sums of
rewards) of making decisions according to a given policy sequence.

Specifically, for a policy sequence |ps : PolicySeq tn| and a reachable,
viable for |n| steps state |x : State t|, we have to compute the value
(in terms of possible sums of rewards) of making |n| decision steps with
|ps| starting from |x|:

<   val : {t : Nat} -> {n : Nat} -> 
<         (x : State t) -> Reachable x -> Viable n x -> PolicySeq t n -> Val

The case |n = Z| (and |ps = Nil|) is trivial. Here, we are not making
any decision step. Thus, we do not collect any reward and the value is
just zero:

<   val {t} {n = Z} x r v ps = zero

If |n = S m| and |ps| consists of a policy |p : Policy t (S m)| and of a
policy sequence |ps : PolicySeq (S t) m|, things are more complicated:

<   val {t} {n = S m} x r v (p :: ps) = ?

Here, we first have to compute the rewards obtained by selecting the
control |y = ctrl (p x r v)| in the first decision step. We get one
possible reward for each state in |nexts t x y|. Thus, if |x' `Elem`
(nexts t x y)|, its corresponding reward is

< reward t x y x'

Next, we have to add to all these rewards (one for every |x'|) the
values of making |m| further decision steps with |ps| starting from
|x'|:

< val x' r' v' ps

To do so, we have to provide reachability and viability evidences |r'|
and |v'| for |x'|. Finally, we have to reduce all possible values to a
single aggregated value. Here is where the measure |meas| comes into
place.

It is useful to introduce the notion of those possible states that can
be obtained by selecting the control |y : Ctrl t x| in |x : State t|:

> PossibleNextState : (x  : State t) -> (y : Ctrl t x) -> Type
> PossibleNextState {t} x y = Sigma (State (S t)) (\ x' => x' `Elem` (nexts t x y))

With this notion in place and assuming 

<   val : {t : Nat} -> {n : Nat} -> 
<         (x : State t) -> Reachable x -> Viable n x -> PolicySeq t n -> Val

to be available, we can easily implement

> mutual

>   sval : (x  : State t) -> (r  : Reachable x) -> (v  : Viable (S m) x) ->
>          (gy  : GoodCtrl t x m) -> (ps : PolicySeq (S t) m) ->
>          PossibleNextState x (ctrl gy) -> Val
>   sval {t} {m} x r v gy ps (MkSigma x' x'emx') = reward t x y x' `plus` val x' r' v' ps where
>     y   : Ctrl t x
>     y   = ctrl gy
>     mx' : M (State (S t))
>     mx' = nexts t x y
>     ar' : All Reachable mx'
>     ar' = reachableSpec1 x r y
>     av' : All (Viable m) mx'
>     av' = allViable gy
>     r'  : Reachable x'
>     r'  = allElemSpec0 x' mx' ar' x'emx'
>     v'  : Viable m x'
>     v'  = allElemSpec0 x' mx' av' x'emx'

And finally

>   val : (x : State t) -> Reachable x -> Viable n x -> PolicySeq t n -> Val
>   val {t} {n = Z} x r v ps = zero
>   val {t} {n = S m} x r v (p :: ps) = meas (fmap (sval x r v gy ps) (tagElem mx')) where
>     gy   :  GoodCtrl t x m
>     gy   =  p x r v
>     y    :  Ctrl t x
>     y    =  ctrl gy
>     mx'  :  M (State (S t))
>     mx'  =  nexts t x y

Notice that in the computation we have used, among others, the following
assumtions from |CoreAssumptions|:

*** That |Val|s can be "added"

*** ...


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
> 
> OptPolicySeq {t} {n} ps  =  (ps' : PolicySeq t n) ->
>                             (x : State t) -> (r : Reachable x) -> (v : Viable n x) ->
>                             val x r v ps' `LTE` val x r v ps

Notice that the above notion of optimality is very strong. It entails a
quantification over all (viable and reachable) states of |Stete t| to
which the first policy of the sequence can be applied. 

Thus, if we manage to compute an optimal policy sequence of length |n|
for making |n| decisions starting from step |t|, we have the guarantee
that, no matter which state we will happen to be at decision step |t|,
there is no better way to make |n| decision steps than that encoded by
our policy.

In other words, we have |n| rules for making "best" (in terms of
"possible" sums of rewards) decisions.

Thus, an obvious question is whether it is at all possible to compute
sequences of policies that are optimal in the above sense. As we shall
see in |FullTheory|, if the assumptions put forward in |FullAssumptions|
are fulfilled, the answer to this question is positive. 

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
> OptExt : PolicySeq (S t) m -> Policy t (S m) -> Type
> OptExt {t} {m} ps p  =  (p' : Policy t (S m)) ->
>                         (x : State t) -> (r : Reachable x) -> (v : Viable (S m) x) ->
>                         val x r v (p' :: ps) `LTE` val x r v (p :: ps)

The idea behind the notion of optimal extension is that if |p| is an
optimal extension of |ps| and |ps| is optimal, then |p :: ps| is optimal.

This is Bellman's principle of optimality [1] which we will implement in
|FullTheory|. There, we will also show that, under the assumptions put
forward in |FullAssumptions|,

> ||| 
> cval : (x  : State t) -> (r  : Reachable x) -> (v  : Viable (S n) x) ->
>        (ps : PolicySeq (S t) n) -> GoodCtrl t x n -> Val
> cval {t} x r v ps gy = meas (fmap (sval x r v gy ps) (tagElem mx')) where
>   y    :  Ctrl t x
>   y    =  ctrl gy
>   mx'  :  M (State (S t))
>   mx'  =  nexts t x y

The result of |cval x r v ps| is the function to be maximized, in order to obtain the best control for the extension of the policy sequence.

The maximization of |cval| is performed by the functions |cvalmax| and |cvalargmax|.  
> cvalmax : (x : State t) -> (r : Reachable x) -> (v : Viable (S n) x)
>           -> (ps : PolicySeq (S t) n) -> Val

> cvalargmax : (x  : State t) -> (r  : Reachable x) -> (v  : Viable (S n) x) ->
>           (ps : PolicySeq (S t) n) -> GoodCtrl t x n

The reason for using these very specific functions, instead of a more general |max| and |argmax|, is that optimisation is, in most case, not computable.  The following assumptions on |cvalmax| and |cvalargmax| are the minimal requirements for the computability of optimal extensions.  Anything more general risks being non-implementable.

> cvalargmaxSpec : {t : Nat} -> {n : Nat} ->
>                  (x  : State t) -> (r  : Reachable x) -> 
>                  (v  : Viable (S n) x) ->  (ps : PolicySeq (S t) n) ->
>                  cvalmax x r v ps = cval x r v ps (cvalargmax x r v ps)

> cvalmaxSpec : {t : Nat} -> {n : Nat} ->
>               (x  : State t) -> (r  : Reachable x) -> 
>               (v  : Viable (S n) x) ->  (ps : PolicySeq (S t) n) ->
>               (y : GoodCtrl t x n) ->
>               (cval x r v ps y) `LTE` (cvalmax x r v ps)

With these assumptions, we can show that

> ||| 
> optExt : PolicySeq (S t) n -> Policy t (S n)
> optExt {t} {n} ps = p where
>   p : Policy t (S n)
>   p x r v = cvalargmax x r v ps

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


> {-

> ---}


[1] Bellman, Richard; "Dynamic Programming", Princeton University Press,
    1957
