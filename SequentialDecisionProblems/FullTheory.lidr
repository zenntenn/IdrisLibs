> module SequentialDecisionProblems.FullTheory

> import SequentialDecisionProblems.CoreTheory

> import Sigma.Sigma
> import Sigma.Operations

> %default total
> %access public export
> %auto_implicits off

> -- %hide Prelude.Nat.LTE


* Preliminaries

In order to prove the correctness of |backwardsInduction| (see
|CoreTheory|), we need a number of additional assumptions, which we
introduce here.  These result in proof obligations for the user of the
framework.  As in |CoreTheory|, they are represented as meta-variables
(or ``holes'').  Once the user has discharged these obligations, type
checking this file will prove the optimality of |backwardsInduction|
(with some caveats related to the current Idris implementation).


* |LTE|

The binary relation introduced in |CoreTheory| for comparing values of
sequences of policies has to be a preorder:

> reflexiveLTE : (a : Val) -> a `LTE` a
> transitiveLTE : (a : Val) -> (b : Val) -> (c : Val) -> a `LTE` b -> b `LTE` c -> a `LTE` c

Additionally, |plus| is required to be monotonic with respect to |LTE|:

> monotonePlusLTE : {a, b, c, d : Val} -> a `LTE` b -> c `LTE` d -> (a `plus` c) `LTE` (b `plus` d)


* |meas|

The function |meas| introduced in |CoreTheory| to describe how a
decision maker measures the possible rewards entailed by (lists,
probability distributions, etc. of) possible next states is required to
fulfill a monotonicity condition:

> measMon  :  {A : Type} ->
>             (f : A -> Val) -> (g : A -> Val) ->
>             ((a : A) -> (f a) `LTE` (g a)) ->
>             (ma : M A) -> meas (fmap f ma) `LTE` meas (fmap g ma)

In a nutshell, |measMon| says that, if |ma| and |mb| are similar
|M|-structures and |ma| is smaller or equal to |mb|, than it cannot be
the case that the measure of |ma| is greater than the measure of |mb|.

This conditions was originally formalized by Ionescu in [2] to give a
consistent meaning to harm measures in vulnerability studies.


* |cvalargmax|

The function |cvalargmax| introduced in |CoreTheory| must deliver
optimal controls.  We need the function |cvalmax|, returning the value
of those optimal controls, in order to fully specify |cvalargmax|:

> cvalmax  :  {t, n : Nat} -> 
>             (x : State t) -> (r : Reachable x) -> (v : Viable (S n) x) ->
>             (ps : PolicySeq (S t) n) -> Val


> cvalargmaxSpec  :  {t : Nat} -> {n : Nat} ->
>                    (x  : State t) -> (r  : Reachable x) -> 
>                    (v  : Viable (S n) x) ->  (ps : PolicySeq (S t) n) ->
>                    cvalmax x r v ps = cval x r v ps (cvalargmax x r v ps)

> cvalmaxSpec  :  {t : Nat} -> {n : Nat} ->
>                 (x  : State t) -> (r  : Reachable x) -> 
>                 (v  : Viable (S n) x) ->  (ps : PolicySeq (S t) n) ->
>                 (y : GoodCtrl t x n) ->
>                 (cval x r v ps y) `LTE` (cvalmax x r v ps)

The reason for using these very specific functions, instead of more
general |argmax|, |max|, |argmaxSpec| and |maxSpec| like for instance

< argmax : {t : Nat} -> {n : Nat} ->
<          (x : State t) -> (Viable (S n) x) ->
<          (f : GoodCtrl t x n -> Val) -> GoodCtrl t x n

< max    : {t : Nat} -> {n : Nat} ->
<          (x : State t) -> (Viable (S n) x) ->
<          (f : GoodCtrl t x n -> Val) -> Val

< argmaxSpec : {t : Nat} -> {n : Nat} ->
<              (x : State t) -> (v : Viable (S n) x) ->
<              (f : GoodCtrl t x n -> Val) ->
<              max x v f = f (argmax x v f)

< maxSpec : {t : Nat} -> {n : Nat} ->
<           (x : State t) -> (v : Viable (S n) x) ->
<           (f : GoodCtrl t x n -> Val) -> (y : GoodCtrl t x n) ->
<           (f y) `LTE` (max x v f)

is that optimisation is, in most case, not computable.  The assumptions
on |cvalmax| and |cvalargmax| are the minimal requirements for the
computability of optimal extensions. Anything more general risks being
non-implementable.


* The proof of correctness of |backwardsInduction|:

** Policy sequences of length zero are optimal

> |||
> nilOptPolicySeq : OptPolicySeq Nil
> nilOptPolicySeq ps' x r v = reflexiveLTE zero


** Bellman's principle of optimality:

> |||
> Bellman  :  {t, m : Nat} -> 
>             (ps  :  PolicySeq (S t) m)  ->   OptPolicySeq ps ->
>             (p   :  Policy t (S m))     ->   OptExt ps p ->
>             OptPolicySeq (p :: ps)

> Bellman {t} {m} ps ops p oep = opps where
>   opps : OptPolicySeq (p :: ps)
>   {-
>   opps (p' :: ps') x r v = transitiveLTE (val x r v (p' :: ps')) 
>                                          (val x r v (p' :: ps)) 
>                                          (val x r v (p :: ps)) 
>                                          s4 s5 where
>   -}
>   opps x r v (p' :: ps') = transitiveLTE (val x r v (p' :: ps')) 
>                                          (val x r v (p' :: ps)) 
>                                          (val x r v (p :: ps)) 
>                                          s4 s5 where
>     gy' : GoodCtrl t x m
>     gy' = p' x r v                       
>     y'  : Ctrl t x
>     y'  = ctrl gy'
>     mx' : M (State (S t))
>     mx' = nexts t x y'
>     av' : All (Viable m) mx'
>     av' = allViable gy'
>     f' : PossibleNextState x (ctrl gy') -> Val
>     f' = sval x r v gy' ps'
>     f  : PossibleNextState x (ctrl gy') -> Val
>     f  = sval x r v gy' ps
>     s1 : (x' : State (S t)) -> (r' : Reachable x') -> (v' : Viable m x') ->
>          val x' r' v' ps' `LTE` val x' r' v' ps
>     -- s1 x' r' v' = ops ps' x' r' v'
>     s1 x' r' v' = ops x' r' v' ps' 
>     s2 : (z : PossibleNextState x (ctrl gy')) -> (f' z) `LTE` (f z)
>     s2 (MkSigma x' x'emx') = 
>       monotonePlusLTE (reflexiveLTE (reward t x y' x')) (s1 x' r' v') where 
>         ar' : All Reachable mx'
>         ar' = reachableSpec1 x r y'
>         r'  : Reachable x'
>         r'  = allElemSpec0 x' mx' ar' x'emx'
>         v'  : Viable m x'
>         v'  = allElemSpec0 x' mx' av' x'emx'
>     s3 : meas (fmap f' (tagElem mx')) `LTE` meas (fmap f (tagElem mx'))
>     s3 = measMon f' f s2 (tagElem mx')
>     s4 : val x r v (p' :: ps') `LTE` val x r v (p' :: ps)
>     s4 = s3
>     s5 : val x r v (p' :: ps) `LTE` val x r v (p :: ps)
>     -- s5 = oep p' x r v
>     s5 = oep x r v p'


> |||
> optExtLemma  :  {t, n : Nat} -> 
>                 (ps : PolicySeq (S t) n) -> OptExt ps (optExt ps)
> {-                
> optExtLemma {t} {n} ps p' x r v = s5 where
>   p     :  Policy t (S n)
>   p     =  optExt ps
>   gy    :  GoodCtrl t x n
>   gy    =  p x r v
>   y     :  Ctrl t x
>   y     =  ctrl gy
>   av    :  All (Viable n) (nexts t x y)
>   av    =  allViable gy
>   gy'   :  GoodCtrl t x n
>   gy'   =  p' x r v
>   y'    :  Ctrl t x
>   y'    =  ctrl gy'
>   av'   :  All (Viable n) (nexts t x y')
>   av'   =  allViable gy'
>   f     :  PossibleNextState x (ctrl gy) -> Val
>   f     =  sval x r v gy ps
>   f'    :  PossibleNextState x (ctrl gy') -> Val
>   f'    =  sval x r v gy' ps
>   s1    :  cval x r v ps gy' `LTE` cvalmax x r v ps
>   s1    =  cvalmaxSpec x r v ps gy'
>   s2    :  cval x r v ps gy' `LTE` cval x r v ps (cvalargmax x r v ps)
>   s2    =  replace {P = \ z => (cval x r v ps gy' `LTE` z)} (cvalargmaxSpec x r v ps) s1
>   -- the rest of the steps are for the (sort of) human reader
>   s3    :  cval x r v ps gy' `LTE` cval x r v ps gy
>   s3    =  s2
>   s4    :  meas (fmap f' (tagElem (nexts t x y'))) `LTE` meas (fmap f (tagElem (nexts t x y)))
>   s4    =  s3
>   s5    :  val x r v (p' :: ps) `LTE` val x r v (p :: ps)
>   s5    =  s4
> -}
> optExtLemma {t} {n} ps x r v p' = s5 where
>   p     :  Policy t (S n)
>   p     =  optExt ps
>   gy    :  GoodCtrl t x n
>   gy    =  p x r v
>   y     :  Ctrl t x
>   y     =  ctrl gy
>   av    :  All (Viable n) (nexts t x y)
>   av    =  allViable gy
>   gy'   :  GoodCtrl t x n
>   gy'   =  p' x r v
>   y'    :  Ctrl t x
>   y'    =  ctrl gy'
>   av'   :  All (Viable n) (nexts t x y')
>   av'   =  allViable gy'
>   f     :  PossibleNextState x (ctrl gy) -> Val
>   f     =  sval x r v gy ps
>   f'    :  PossibleNextState x (ctrl gy') -> Val
>   f'    =  sval x r v gy' ps
>   s1    :  cval x r v ps gy' `LTE` cvalmax x r v ps
>   s1    =  cvalmaxSpec x r v ps gy'
>   s2    :  cval x r v ps gy' `LTE` cval x r v ps (cvalargmax x r v ps)
>   s2    =  replace {P = \ z => (cval x r v ps gy' `LTE` z)} (cvalargmaxSpec x r v ps) s1
>   -- the rest of the steps are for the (sort of) human reader
>   s3    :  cval x r v ps gy' `LTE` cval x r v ps gy
>   s3    =  s2
>   s4    :  meas (fmap f' (tagElem (nexts t x y'))) `LTE` meas (fmap f (tagElem (nexts t x y)))
>   s4    =  s3
>   s5    :  val x r v (p' :: ps) `LTE` val x r v (p :: ps)
>   s5    =  s4

** Correctness of backwards induction

> backwardsInductionLemma : (t : Nat) -> (n : Nat) -> OptPolicySeq (backwardsInduction t n)
> backwardsInductionLemma t  Z     =  nilOptPolicySeq
> backwardsInductionLemma t (S n)  =  Bellman ps ops p oep where
>   ps   :  PolicySeq (S t) n
>   ps   =  backwardsInduction (S t) n
>   ops  :  OptPolicySeq ps
>   ops  =  backwardsInductionLemma (S t) n
>   p    :  Policy t (S n)
>   p    =  optExt ps
>   oep  :  OptExt ps p
>   oep  =  optExtLemma ps

Thus, we can compute provably optimal sequences of policies for
arbitrary SDPs and number of decision steps. 


> {-

> ---}


[1] Bellman, Richard; "Dynamic Programming", Princeton University Press,
    1957

[2] Ionescu, Cezar; "Vulnerability Modelling and Monadic Dynamical
    Systems", Freie Universitaet Berlin, 2009
