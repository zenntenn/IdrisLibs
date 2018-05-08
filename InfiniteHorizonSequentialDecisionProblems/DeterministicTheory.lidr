> module InfiniteHorizonSequentialDecisionProblems.DeterministicTheory

> import Data.Vect

> import Finite.Predicates
> import Finite.Operations
> import Finite.Properties
> import Vect.Operations

> %default total
> %access public export
> %auto_implicits off


* Sequential decision processes

> State  :  Type
> Ctrl   :  (x : State) -> Type
> next   :  (x : State) -> (y : Ctrl x) -> State


* Sequential decision problems

> Val              :  Type
> reward           :  (x : State) -> (y : Ctrl x) -> (x' : State) -> Val
> (<+>)            :  Val -> Val -> Val
> LTE              :  Val -> Val -> Type


* Policies

> Policy  :  Type
> Policy  =  (x : State) -> Ctrl x


* The value of policies

> ||| A value function ...
> val : State -> Policy -> Val

> ||| ... that fulfils the specification
> valSpec  :  Type
> valSpec  =  (x : State) -> (p : Policy) -> 
>             val x p = reward x (p x) (next x (p x)) <+> val (next x (p x)) p


* Optimality of policies

> |||
> Opt    :  Policy -> Type
> Opt p  =  (x : State) -> (p' : Policy) -> val x p' `LTE` val x p


* Optimal policies

> ||| 
> cval        :  (x : State) -> Ctrl x -> (p : Policy) -> Val
> cval x y p  =  reward x y (next x y) <+> val (next x y) p

> cvalargmax      :  (x : State) -> (p : Policy) -> Ctrl x

> ||| A policy ...
> opt : Policy

> ||| ... that fulfils Bellman's equation
> optSpec  :  Type
> optSpec  =  (x : State) -> opt x = cvalargmax x opt  


* Optimality of |opt|

** Additional assumptions

> reflexiveLTE     :  (a : Val) -> a `LTE` a
> transitiveLTE    :  {a, b, c : Val} -> a `LTE` b -> b `LTE` c -> a `LTE` c
> monotonePlusLTE  :  {a, b, c, d : Val} -> a `LTE` b -> c `LTE` d -> (a <+> c) `LTE` (b <+> d)

> cvalmax         :  (x : State) -> (p : Policy) -> Val
> cvalargmaxSpec  :  (x : State) -> (p : Policy) -> cvalmax x p = cval x (cvalargmax x p) p
> cvalmaxSpec     :  (x : State) -> (y : Ctrl x) -> (p : Policy) -> (cval x y p) `LTE` (cvalmax x p)


** |opt| is optimal

> mutual

>   ||| ... is an optimal policy
>   optLemma1  :  (vs : valSpec) -> (os : optSpec) ->
>                 (x : State) -> (y : Ctrl x) -> (p : Policy) -> 
>                 cval x y p `LTE` cval x y opt
>   optLemma1 vs os x y p = s3 where
>     x' : State
>     x' = next x y
>     s1 : val x' p `LTE` val x' opt
>     s1 = assert_total (optLemma2 vs os) x' p
>     s2 : reward x y x' <+> val x' p `LTE` reward x y x' <+> val x' opt
>     s2 = monotonePlusLTE (reflexiveLTE (reward x y x')) s1
>     s3 : cval x y p `LTE` cval x y opt
>     s3 = s2

>   ||| ... is an optimal policy
>   optLemma2 : (vs : valSpec) -> (os : optSpec) -> Opt opt
>   optLemma2 vs os x p' = s9 where
>     s1 : val x p' = cval x (p' x) p'
>     s1 = vs x p'
>     s2 : cval x (p' x) p' `LTE` cval x (p' x) opt
>     s2 = assert_total optLemma1 vs os x (p' x) p'
>     s3 : cval x (p' x) opt `LTE` cvalmax x opt
>     s3 = cvalmaxSpec x (p' x) opt
>     s4 : cvalmax x opt = cval x (cvalargmax x opt) opt
>     s4 = cvalargmaxSpec x opt
>     s5 : cval x (cvalargmax x opt) opt = cval x (opt x) opt
>     s5 = replace {P = \ U => cval x U opt = cval x (opt x) opt} (os x) Refl
>     s6 : cval x (opt x) opt = val x opt
>     s6 = sym (vs x opt)
>     s7 : cval x (p' x) p' `LTE` cvalmax x opt
>     s7 = transitiveLTE s2 s3
>     s8 : val x p' `LTE` cvalmax x opt
>     s8 = replace {P = \ W => W `LTE` cvalmax x opt} (sym s1) s7
>     s9 : val x p' `LTE` val x opt
>     s9 = replace {P = \ W => val x p' `LTE` W} (trans (trans s4 s5) s6) s8


* Can one compute optimal policies?

If |State| is finite

> finiteState : Finite State

we can compute the number of values of type |State| and collect them in
a vector

> cardState : Nat
> cardState = card finiteState

> vectState : Vect cardState State
> vectState = toVect finiteState

For a fixed policy |p|, we can represent the value of |p| by a value table

> vt : Policy -> Vect cardState Val

> val x p = index k (vt p) where
>   k : Fin cardState
>   k = lookup x vectState (toVectComplete finiteState x)

In this case, the specification of |val| 

< valSpec  :  Type
< valSpec  =  (x : State) -> (p : Policy) -> 
<             val x p = reward x (p x) (next x (p x)) <+> val (next x (p x)) p

defines a linear, implicit problem for the components |vt p|. Let

> nextR : (k : Fin cardState) -> (y : Ctrl (index k vectState)) -> Fin cardState
> nextR k y = lookup x' vectState (toVectComplete finiteState x') where
>   x' : State
>   x' = next (index k vectState) y

> rewardR : (k : Fin cardState) -> (y : Ctrl (index k vectState)) -> Val
> rewardR k y = reward (index k vectState) y (next (index k vectState) y)

We write |valSpec x p| for the components of |vectState|. For the |k|-th
component, we have

val (index k vectState) p 
  = 
reward (index k vectState) (p (index k vectState)) (next (index k vectState) (p (index k vectState))) 
<+> 
val (next (index k vectState) (p (index k vectState))) p

val (index k vectState) p 
  = { def. val }
index (lookup (index k vectState) vectState (toVectComplete finiteState (index k vectState))) (vt p)
  = { lookup-index property} 
index k (vt p)

reward (index k vectState) (p (index k vectState)) (next (index k vectState) (p (index k vectState))) 
  = { let pR = \ k => p (index k vectState) }
reward (index k vectState) (pR k) (next (index k vectState) (pR k)) 
  = { def. rewardR }
rewardR k (pR k)

val (next (index k vectState) (p (index k vectState))) p
  = { let pR = \ k => p (index k vectState) }
val (next (index k vectState) (pR k)) p
  = { def. val }
index (lookup (next (index k vectState) (pR k)) vectState (toVectComplete finiteState (next (index k vectState) (pR k)))) (vt p)
  = { def. nextR } 
index (nextR k (pR k)) (vt p)

Thus, the equations for |vt|

\ k => index k (vt p) = rewardR k (pR k) <+> index (nextR k (pR k)) (vt p)

define a sparse matrix with only two entries per row. 




> {-

> ---}


