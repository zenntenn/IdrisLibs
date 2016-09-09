> module SequentialDecisionProblems.Generic.FullTheory

> import SequentialDecisionProblems.Generic.CoreAssumptions
> import SequentialDecisionProblems.Generic.ExtraAssumptions
> import SequentialDecisionProblems.Generic.CoreTheory

> import Sigma.Sigma
> import Sigma.Operations

> %default total
> %access public export
> %auto_implicits on


* The full theory of monadic sequential decision problems (SDP):


** Policy sequences of length zero are optimal

> |||
> nilOptPolicySeq : OptPolicySeq Nil
> nilOptPolicySeq ps' x r v = reflexiveLTE zero


** Bellman's principle of optimality:

> |||
> Bellman  :  (ps  :  PolicySeq (S t) m)  ->   OptPolicySeq ps ->
>             (p   :  Policy t (S m))     ->   OptExt ps p ->
>             OptPolicySeq (p :: ps)

> Bellman {t} {m} ps ops p oep = opps where
>   opps : OptPolicySeq (p :: ps)
>   opps (p' :: ps') x r v = transitiveLTE (val x r v (p' :: ps')) 
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
>     s1 x' r' v' = ops ps' x' r' v'
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
>     s5 = oep p' x r v


> |||
> optExtLemma : (ps : PolicySeq (S t) n) -> OptExt ps (optExt ps)
> optExtLemma {t} {n} ps p' x r v = s6 where
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
>   g     :  GoodCtrl t x n -> Val
>   g     =  cval x r v ps
>   f     :  PossibleNextState x (ctrl gy) -> Val
>   f     =  sval x r v gy ps
>   f'    :  PossibleNextState x (ctrl gy') -> Val
>   f'    =  sval x r v gy' ps
>   s1    :  g gy' `LTE` max x v g
>   s1    =  maxSpec x v g gy'
>   s2    :  g gy' `LTE` g (argmax x v g)
>   s2    =  replace {P = \ z => (g gy' `LTE` z)} (argmaxSpec x v g) s1
>   -- the rest of the steps are for the (sort of) human reader
>   s3    :  g gy' `LTE` g gy
>   s3    =  s2
>   s4    :  cval x r v ps gy' `LTE` cval x r v ps gy
>   s4    =  s3
>   s5    :  meas (fmap f' (tagElem (nexts t x y'))) `LTE` meas (fmap f (tagElem (nexts t x y)))
>   s5    =  s4
>   s6    :  val x r v (p' :: ps) `LTE` val x r v (p :: ps)
>   s6    =  s5

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
