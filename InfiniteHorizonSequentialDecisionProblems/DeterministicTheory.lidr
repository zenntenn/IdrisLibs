> module InfiniteHorizonSequentialDecisionProblems.DeterministicTheory

> import Data.Vect
> import Syntax.PreorderReasoning

> import Finite.Predicates
> import Finite.Operations
> import Finite.Properties
> import Vect.Operations
> import Vect.Properties

> %default total
> %access public export
> %auto_implicits off

* -----------------------------
* Sequential decision processes
* -----------------------------

> State  :  Type
> Ctrl   :  (x : State) -> Type
> next   :  (x : State) -> (y : Ctrl x) -> State


* ----------------------------
* Sequential decision problems
* ----------------------------

> Val              :  Type
> reward           :  (x : State) -> (y : Ctrl x) -> (x' : State) -> Val
> (<+>)            :  Val -> Val -> Val
> LTE              :  Val -> Val -> Type


* --------
* Policies
* --------

> Policy  :  Type
> Policy  =  (x : State) -> Ctrl x


* ---------------------
* The value of policies
* ---------------------

The value of making infinite many decision steps with a policy by
starting from a given state is given by a "value" function

> val : Policy -> State -> Val

that fulfils the specification

> valSpec  :  Type
> valSpec  =  (p : Policy) -> (x : State) -> 
>             val p x = reward x (p x) (next x (p x)) <+> val p (next x (p x))

A naive attempt at implementing |val| directly "from its specification"

< val p x = reward x (p x) (next x (p x)) <+> val p (next x (p x))

yiels a possibly non total function. In contrast to SDPs with a finite
number of decision steps, we cannot rely on an induction principle for
decision problems over an infinite number of steps. Obviously, there are
cases in which |val| can be implemented. For instance, if all states
have the same successor. An important is when |State| is finite. We
discuss this case below.


* ----------------------
* Optimality of policies
* ----------------------

> Opt    :  Policy -> Type
> Opt p  =  (p' : Policy) -> (x : State) -> val p' x `LTE` val p x


* ----------------
* Optimal policies
* ----------------

Let |LTE| be a preorder

> reflexiveLTE     :  (a : Val) -> a `LTE` a
> transitiveLTE    :  {a, b, c : Val} -> a `LTE` b -> b `LTE` c -> a `LTE` c

and let |<+>| be monotonous w.r.t. |LTE|

> monotonePlusLTE  :  {a, b, c, d : Val} -> a `LTE` b -> c `LTE` d -> (a <+> c) `LTE` (b <+> d)

We can compute the value of making a first decision step with a given
control and then infinitely many further steps with a given policy in
terms of the (yet to be implemented) |val| function:

> cval        :  (p : Policy) -> (x : State) -> Ctrl x -> Val
> cval p x y  =  reward x y (next x y) <+> val p (next x y)

Assume that, for an arbitrary policy |p| and for an arbitrary state |x|,
we can pick up a control that maximises |cval p x|:

> cvalmax         :  (p : Policy) -> (x : State) -> Val
> cvalargmax      :  (p : Policy) -> (x : State) -> Ctrl x

> cvalargmaxSpec  :  (p : Policy) -> (x : State) -> cvalmax p x = cval p x (cvalargmax p x)
> cvalmaxSpec     :  (p : Policy) -> (x : State) -> (y : Ctrl x) -> cval p x y `LTE` cvalmax p x

This is certainly the case if |Ctrl x| is non empty and finite for any
|x| but there are more interesting cases in which we can compute "best"
controls. In these cases, a policy

> opt : Policy

that fulfils Bellman's equation

> optSpec  :  Type
> optSpec  =  (x : State) -> opt x = cvalargmax opt x  

is optimal

> optLemma : (vs : valSpec) -> (os : optSpec) -> Opt opt

As in the case of |val|, we cannot implement |optLemma| in general. But
it is useful to look at a (possibly non total) implementation:

> optLemma vs os p' x = s9 where
>   s1 : val p' (next x (p' x)) `LTE` val opt (next x (p' x))
>   s1 = assert_total (optLemma vs os p' (next x (p' x)))
>   s2 : cval p' x (p' x) `LTE` cval opt x (p' x)
>   s2 = monotonePlusLTE (reflexiveLTE (reward x (p' x) (next x (p' x)))) s1
>   s3 : cval opt x (p' x) `LTE` cvalmax opt x
>   s3 = cvalmaxSpec opt x (p' x)
>   s4 : cvalmax opt x = cval opt x (cvalargmax opt x)
>   s4 = cvalargmaxSpec opt x
>   s5 : cval opt x (cvalargmax opt x) = cval opt x (opt x)
>   s5 = replace {P = \ U => cval opt x U = cval opt x (opt x)} (os x) Refl
>   s6 : cval opt x (opt x) = val opt x
>   s6 = sym (vs opt x)
>   s7 : cval p' x (p' x) `LTE` cvalmax opt x
>   s7 = transitiveLTE s2 s3
>   s8 : val p' x `LTE` cvalmax opt x
>   s8 = replace {P = \ W => W `LTE` cvalmax opt x} (sym (vs p' x)) s7
>   s9 : val p' x `LTE` val opt x
>   s9 = replace {P = \ W => val p' x `LTE` W} (trans (trans s4 s5) s6) s8


* -------------------------
* The case of finite states
* -------------------------

If |State| is finite

> finiteState : Finite State

we can compute the number of values of type |State| 

> cardState : Nat
> cardState = card finiteState

and collect them in a vector

> vectState : Vect cardState State
> vectState = toVect finiteState

This representation of |State| is guaranteed to be complete

> completeVectState : (x : State) -> Elem x vectState
> completeVectState = toVectComplete finiteState

We can also represent the value of a policy by a value table

> vt : Policy -> Vect cardState Val

and implement |val| in terms of the values of the table

> val p x = index k (vt p) where
>   k : Fin cardState
>   k = lookup x vectState (completeVectState x)

In this case, the specification of |val| defines a linear system of
equations for the components of the value table. To derive these
equations, consider, first the representation of |next|

> nextR : (k : Fin cardState) -> (y : Ctrl (index k vectState)) -> Fin cardState
> nextR k y = lookup x' vectState (completeVectState x') where
>   x' : State
>   x' = next (index k vectState) y

|nextR| is a representations of |next| in the sense that

> nextLemma  : (k : Fin cardState) -> (y : Ctrl (index k vectState)) ->
>              index (nextR k y) vectState = next (index k vectState) y

A proof of |nextLemma| is straightforward, see Appendix below. It is
also useful to define a representation for the reward function

> rewardR : (k : Fin cardState) -> (y : Ctrl (index k vectState)) -> Val
> rewardR k y = reward x y (next x y) where
>   x : State
>   x = index k vectState

and for policies:

> pR : (p : Policy) -> (k : Fin cardState) -> Ctrl (index k vectState)
> pR p k = p (index k vectState) 

With |nextR|, |rewardR| and |pR|, we can derive the system of equations for
the components of |vt| by rewriting |valSpec p| for each component of
|vectSpace|:

> equation : (vs : valSpec) -> (p : Policy) -> (k : Fin cardState) -> 
>            index k (vt p) 
>            = 
>            rewardR k (pR p k) <+> index (nextR k (pR p k)) (vt p)

To derive |equation|, it is useful to prove three intermediate results:

> lemma1 : (p : Policy) -> (k : Fin cardState) -> index k (vt p) = val p (index k vectState)

> lemma2 : (p : Policy) -> (k : Fin cardState) -> 
>          reward (index k vectState) (p (index k vectState)) (next (index k vectState) (p (index k vectState)))
>          =
>          rewardR k (pR p k)
> lemma2 p k = Refl

> lemma3 : (p : Policy) -> (k : Fin cardState) -> 
>          val p (next (index k vectState) (p (index k vectState)))
>          =
>          index (nextR k (pR p k)) (vt p)

> equation vs p k = let x = index k vectState in
>                   ( index k (vt p) )
>                 ={ lemma1 p k }=
>                   ( val p x )
>                 ={ vs p x }=
>                   ( reward x (p x) (next x (p x)) <+> val p (next x (p x)) )
>                 ={ replace {P = \ W => reward x (p x) (next x (p x)) <+> val p (next x (p x)) = W <+> val p (next x (p x))} (lemma2 p k) Refl }=
>                   ( rewardR k (pR p k) <+> val p (next x (p x)) )
>                 ={ replace {P = \ W => rewardR k (pR p k) <+> val p (next x (p x)) = rewardR k (pR p k) <+> W} (lemma3 p k) Refl }=
>                   ( rewardR k (pR p k) <+> index (nextR k (pR p k)) (vt p) )
>                 QED


val (index k vectState) p 
  = { def. val }
index (lookup (index k vectState) vectState (toVectComplete finiteState (index k vectState))) (vt p)
  = { lookup-index property} 
index k (vt p)

val (next (index k vectState) (p (index k vectState))) p
  = { let pR = \ k => p (index k vectState) }
val (next (index k vectState) (pR k)) p
  = { def. val }
index (lookup (next (index k vectState) (pR k)) vectState (toVectComplete finiteState (next (index k vectState) (pR k)))) (vt p)
  = { def. nextR } 
index (nextR k (pR k)) (vt p)


* --------
* Appendix
* --------

> nextLemma k y = ( index (nextR k y) vectState )
>               ={ Refl }=
>                 ( index (lookup (next (index k vectState) y) vectState (completeVectState (next (index k vectState) y))) vectState )
>               ={ indexLookupLemma (next (index k vectState) y) vectState (completeVectState (next (index k vectState) y)) }=
>                 ( next (index k vectState) y )
>               QED



> {-

> ---}


 
 
