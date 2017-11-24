> module SequentialDecisionGames.CoreTheory

> import Sigma.Sigma
> import Sigma.Operations

> %default total
> %access public export
> %auto_implicits off


* Preliminaries

For the time being, we just consider two players: player 1 and player 2



* Sequential decision processes

> State : (t : Nat) -> Type

|Ctrl1 t x| and |Ctrl2 t x| are the controls available to player 1 and
 to player 2 at decision step |t| and in state |x|:

> Ctrl1 : (t : Nat) -> (x : State t) -> Type
> Ctrl2 : (t : Nat) -> (x : State t) -> Type

> M : Type -> Type

> nexts : (t : Nat) -> 
>         (x : State t) -> 
>         (Ctrl1 t x, Ctrl2 t x) -> 
>         M (State (S t))

> fmap  :  {A, B : Type} -> 
>          (A -> B) -> M A -> M B
> postulate functorSpec1  :  fmap . id = id
> postulate functorSpec2  :  {A, B, C : Type} -> {f : B -> C} -> {g : A -> B} ->
>                            fmap (f . g) = (fmap f) . (fmap g)



* Sequential decision problems

> Val : Type

> reward : (t : Nat) -> 
>          (x : State t) -> 
>          (Ctrl1 t x, Ctrl2 t x) -> 
>          (x' : State (S t)) -> (Val, Val)

> plus : Val -> Val -> Val

> zero : Val

> LTE : Val -> Val -> Type

> meas1 : M Val -> Val
> meas2 : M Val -> Val


* Solving sequential decision problems

> Elem     : {A : Type} -> A -> M A -> Type
> NotEmpty : {A : Type} -> M A -> Type
> All      : {A : Type} -> (P : A -> Type) -> M A -> Type
> tagElem  : {A : Type} -> (ma : M A) -> M (Sigma A (\ a => a `Elem` ma))

> allElemSpec0                 :  {A : Type} -> {P : A -> Type} ->
>                                 (a : A) -> (ma : M A) -> All P ma -> a `Elem` ma -> P a

> postulate elemNotEmptySpec0  :  {A : Type} -> 
>                                 (a : A) -> (ma : M A) -> a `Elem` ma -> NotEmpty ma

> postulate elemNotEmptySpec1  :  {A : Type} -> 
>                                 (ma : M A) -> NotEmpty ma -> Sigma A (\ a => a `Elem` ma)


> postulate tagElemSpec        :  {A : Type} -> (ma : M A) -> fmap outl (tagElem ma) = ma



* Viability

> Viable : {t : Nat} -> (n : Nat) -> State t -> Type

> postulate viableSpec0 : {t : Nat} ->
>                         (x : State t) -> Viable Z x

> Good : (t : Nat) -> (x : State t) -> (n : Nat) -> (Ctrl1 t x, Ctrl2 t x) -> Type
> Good t x n y = (NotEmpty (nexts t x y), All (Viable {t = S t} n) (nexts t x y))

> GoodCtrl : (t : Nat) -> (x : State t) -> (n : Nat) -> Type
> GoodCtrl t x n = Sigma ((Ctrl1 t x), (Ctrl2 t x)) (Good t x n)

> viableSpec1 : {t : Nat} -> {n : Nat} ->
>               (x : State t) -> Viable (S n) x -> GoodCtrl t x n

> postulate viableSpec2 : {t : Nat} -> {n : Nat} ->
>                         (x : State t) -> GoodCtrl t x n -> Viable (S n) x

> ctrl : {t, n : Nat} -> {x : State t} -> GoodCtrl t x n -> (Ctrl1 t x, Ctrl2 t x)
> ctrl (MkSigma y _) = y

> allViable : {t, n : Nat} -> {x : State t} -> 
>             (gy : GoodCtrl t x n) -> 
>             All (Viable {t = S t} n) (nexts t x (ctrl gy)) 
> allViable (MkSigma _ p) = snd p


> {-

* Reachability

Viability is, strictly speaking, all what is needed to formalize the
notion of policies as functions that associate "good" controls to
viable states.

But in a decision problem, not all viable states are actually
reachable. Thus, we would like to further restrict the domain of
policies to states that can actually be reached. Intuitively, a state is
reachable if there are controls that allow for a path from some initial
state to that state. Thus, tautologically, every initial state is
reachable:

> Reachable : {t' : Nat} -> State t' -> Type

> postulate reachableSpec0 : (x : State Z) -> Reachable x

Moreover, if |x| is reachable and admits a control |y|, then all states
that can be obtained by selecting |y| in |x| are also reachable:

> reachableSpec1  :  {t : Nat} -> (x : State t) -> Reachable x -> (y : Ctrl t x) -> All Reachable (nexts t x y)

And the other way round:

> Pred : {t : Nat} -> State t -> State (S t) -> Type
> Pred {t} x x'  =  Sigma (Ctrl t x) (\ y => x' `Elem` nexts t x y)

> ReachablePred : {t : Nat} -> State t -> State (S t) -> Type
> ReachablePred x x'  = (Reachable x, x `Pred` x')

> postulate reachableSpec2  :  {t : Nat} -> (x' : State (S t)) -> Reachable x' -> Sigma (State t) (\ x => x `ReachablePred` x')


* Policies and policy sequences

Policies are functions that associate to every state |x| at decision
step |t| which is reachable and viable for |S m| steps (from which |S
m| more decision steps are doable) a good control:

> Policy : (t : Nat) -> (n : Nat) -> Type
> Policy t Z      =  Unit
> Policy t (S m)  =  (x : State t) -> Reachable x -> Viable (S m) x -> GoodCtrl t x m

A policy sequence for making |n| decision steps starting from some
(reachable, viable for |n| steps) state at decision step |t| is a list
of policies of length |n|, one for each decision step:

> data PolicySeq : (t : Nat) -> (n : Nat) -> Type where
>   Nil   :  {t : Nat} -> 
>            PolicySeq t Z
>   (::)  :  {t, n : Nat} -> 
>            Policy t (S n) -> PolicySeq (S t) n -> PolicySeq t (S n)

Fold for |PolicySeq|:

> foldPolicySeq : {X : (t : Nat) -> (n : Nat) -> Type} ->
>                 ((t : Nat) -> X t Z) ->
>                 ((t : Nat) -> (n : Nat) -> Policy t (S n) -> X (S t) n -> X t (S n)) ->
>                 (t : Nat) -> (n : Nat) -> PolicySeq t n -> X t n
> foldPolicySeq e f t Z Nil = e t
> foldPolicySeq e f t (S n) (p :: ps) = f t n p (foldPolicySeq e f (S t) n ps)

* The value of policy sequences

As mentioned before, the idea of a decision problem is that the
decision maker seeks controls that maximize the sum of the rewards
obtained in a decision process.

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

> PossibleNextState  :  {t : Nat} -> 
>                       (x  : State t) -> (y : Ctrl t x) -> Type
> PossibleNextState {t} x y = Sigma (State (S t)) (\ x' => x' `Elem` (nexts t x y))

With this notion in place and assuming 

<   val : {t : Nat} -> {n : Nat} -> 
<         (x : State t) -> Reachable x -> Viable n x -> PolicySeq t n -> Val

to be available, we can implement

> mutual

>   sval  :  {t, m : Nat} -> 
>            (x  : State t) -> (r  : Reachable x) -> (v  : Viable (S m) x) ->
>            (gy  : GoodCtrl t x m) -> (ps : PolicySeq (S t) m) ->
>            PossibleNextState x (ctrl gy) -> Val
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

>   val  :  {t, n : Nat} -> 
>           (x : State t) -> (r : Reachable x) -> (v : Viable n x) -> PolicySeq t n -> Val
>   val {t} {n = Z} x r v ps = zero
>   val {t} {n = S m} x r v (p :: ps) = meas (fmap (sval x r v gy ps) (tagElem mx')) where
>     gy   :  GoodCtrl t x m
>     gy   =  p x r v
>     y    :  Ctrl t x
>     y    =  ctrl gy
>     mx'  :  M (State (S t))
>     mx'  =  nexts t x y


* Optimality of policy sequences

With a function for computing the value (in terms of "possible" sums
of rewards) of making |n| decision steps with a policy sequence
starting from some specific state, we can formalise what it means for
one such sequence to be optimal.

Informally, we say that a policy sequence |ps| for making |n| decision
steps starting from states in |State t| which are reachable and viable
for |n| steps is optimal if its value is at least as good as the value
of any other policy sequence for making |n| decision steps starting
from states in |State t|. Formally:

> |||
> OptPolicySeq  :  {t, n : Nat} -> 
>                  PolicySeq t n -> Type
> 
> {-
> OptPolicySeq {t} {n} ps  =  (ps' : PolicySeq t n) ->
>                             (x : State t) -> (r : Reachable x) -> (v : Viable n x) ->
>                             val x r v ps' `LTE` val x r v ps
> -}
> OptPolicySeq {t} {n} ps  =  (x : State t) -> (r : Reachable x) -> (v : Viable n x) ->
>                             (ps' : PolicySeq t n) ->
>                             val x r v ps' `LTE` val x r v ps

Notice that the above notion of optimality is very strong. It entails a
quantification over all (viable and reachable) states of |Stete t| to
which the first policy of the sequence can be applied. 

Thus, if we manage to compute an optimal policy sequence of length |n|
for making |n| decisions starting from step |t|, we have the guarantee
that, no matter which state we will happen to be at decision step |t|,
there is no better way to make |n| decision steps than that encoded by
our policy.

In other words, we have |n| rules for making ``best'' (in terms of
``possible'' sums of rewards) decisions.

Thus, an obvious question is whether it is at all possible to compute
sequences of policies that are optimal in the above sense. As we shall
see in |FullTheory|, if the assumptions put forward here and in
|ExtraAssumptions| are fulfilled, the answer to this question is
positive.

In the rest of this file, we implement a generic backwards induction
algorithm for computing optimal policy sequences for an arbitrary number
of decision steps.


* Optimal extensions of policy sequences

The computation at the core of backwards induction is the computation
of an optimal extension of a policy sequence. An extension of a policy
sequence for making |m| decision steps starting from states at
decision step |S t| is just a policy for taking decisions at step |t|,
that is, a policy that is put *in front* of the list of policies that
will deal with any resulting future states.

Informally, a policy |p| is an optimal extension of a policy sequence
|ps| if there is no better way than |p :: ps| to make |S m| decision
steps at step |t|. Formally:

> |||
> OptExt  :  {t, m : Nat} -> 
>            PolicySeq (S t) m -> Policy t (S m) -> Type
> {-           
> OptExt {t} {m} ps p  =  (p' : Policy t (S m)) ->
>                         (x : State t) -> (r : Reachable x) -> (v : Viable (S m) x) ->
>                         val x r v (p' :: ps) `LTE` val x r v (p :: ps)
> -}
> OptExt {t} {m} ps p  =  (x : State t) -> (r : Reachable x) -> (v : Viable (S m) x) ->
>                         (p' : Policy t (S m)) ->
>                         val x r v (p' :: ps) `LTE` val x r v (p :: ps) 

The idea behind the notion of optimal extension is that if |p| is an
optimal extension of |ps| and |ps| is optimal, then |p :: ps| is
optimal.  This is Bellman's principle of optimality [1] which we will
implement in |FullTheory|.

The strong requirement of optimality implies that |p| is optimal for
every state, therefore, the control obtained by applying |p| to a given
state |x| must be optimal, i.e., it must maximise the function |cval x r
v ps|:

> ||| 
> cval  :  {t, n : Nat} -> 
>          (x : State t) -> (r : Reachable x) -> (v : Viable (S n) x) ->
>          (ps : PolicySeq (S t) n) -> GoodCtrl t x n -> Val
> cval {t} x r v ps gy = meas (fmap (sval x r v gy ps) (tagElem mx')) where
>   y    :  Ctrl t x
>   y    =  ctrl gy
>   mx'  :  M (State (S t))
>   mx'  =  nexts t x y

Let |cvalargmax| be a function that delivers the control that leads to
the maximal value of |cval x r v ps|:

> cvalargmax  :  {t, n : Nat} -> 
>                (x  : State t) -> (r : Reachable x) -> (v : Viable (S n) x) ->
>                (ps : PolicySeq (S t) n) -> GoodCtrl t x n

The controls obtained by maximising |cval x r v ps| for each of the
states |x : State t| will deliver a policy which is an optimal extension
of |ps|.  Thus, the problem of maximising |val| has been reduced to the
maximisation of |cval| for the states at time |t|.  Therefore, the
function that computes this optimal extension is:

> ||| 
> optExt  :  {t, n : Nat} -> 
>            PolicySeq (S t) n -> Policy t (S n)
> optExt {t} {n} ps = p where
>   p : Policy t (S n)
>   p x r v = cvalargmax x r v ps


* Generic machine checkable backwards induction

If |LTE| is reflexive, it is straightforward to show that empty policy
sequences (that is, sequences for performing zero decision steps) are
optimal. Therefore, we have a starting point for the recursive process
of extending optimal policy sequences. This suggests the following
implementations of backwards induction:

> backwardsInduction : (t : Nat) -> (n : Nat) -> PolicySeq t n
> backwardsInduction t  Z     =  Nil
> backwardsInduction t (S n)  =  optExt ps :: ps where
>   ps : PolicySeq (S t) n
>   ps = backwardsInduction (S t) n

> {-

> take : {t : Nat} -> (n : Nat) -> (m : Nat) -> PolicySeq t n -> Sigma Nat (\ m' => PolicySeq t m')
> take {t}    Z   m          ps  = MkSigma Z Nil
> take {t} (S n)  Z          ps  = MkSigma Z Nil
> take {t} (S n) (S m) (p :: ps) = MkSigma (S m') (p' :: ps') where
>   mps' : Sigma Nat (\ m' => PolicySeq (S t) m')
>   mps' = take n m ps 
>   m'   : Nat
>   m'   = outl mps'
>   ps'  : PolicySeq (S t) m'
>   ps'  = outr mps'
>   p'   : Policy t (S m')
>   p'   = ?this_might_work -- p

> bi : (t : Nat) -> (n : Nat) -> (m : Nat) -> PolicySeq t n
> bi t  Z    m  =  Nil
> bi t (S n) m  =  p :: ps where
>   ps        : PolicySeq (S t) n
>   ps        = bi (S t) n m
>   m'        : Nat 
>   m'        = outl (take n m ps)
>   ps'       : PolicySeq (S t) m'
>   ps'       = outr (take n m ps)
>   p         : Policy t (S n)
>   p         = ?this_will_not_work -- optExt ps'

> -}

This file contains all the *computational* elements that the user must
specify in order to be able to run |backwardsInduction|.  The results
are going to fulfill the condition of optimality only if several
assumptions hold, some of which we have introduced only informally (and
others not at all).  For example, we have not formalised the requirement
that |cvalargmax| delivers an optimal control, or that |LTE| is
reflexive (and we haven't even mentioned its transitivity, which is also
required).

These additional assumptions are formulated in the file |FullTheory|,
where we also implement a machine-checked proof of the correctness of
|backwardsInduction| under these assumptions.

This separation has been introduced in order to enable users that do not
want to deal with formal proofs to use the framework for computing
optimal policies.  Of course, the optimality of the results will, in
this case, not be machine-checked.


> ---}

