> module SequentialDecisionProblems.Deterministic.FullTheory

> import SequentialDecisionProblems.Deterministic.CoreAssumptions
> import SequentialDecisionProblems.Deterministic.ExtraAssumptions
> import SequentialDecisionProblems.Deterministic.CoreTheory

> import Sigma.Sigma
> import Sigma.Operations

> %default total
> %access public export
> %auto_implicits off


* The full theory of monadic sequential decision problems (SDP):


** Policy sequences of length zero are optimal

> |||
> nilOptPolicySeq : OptPolicySeq Nil
> nilOptPolicySeq ps' x r v = reflexiveLTE zero


** Bellman's principle of optimality:

> |||
> Bellman : {t : Nat} -> {m : Nat} -> 
>           (ps  : PolicySeq (S t) m)  ->   OptPolicySeq ps ->
>           (p   : Policy t (S m))     ->   OptExt ps p ->
>           OptPolicySeq (p :: ps)

> Bellman {t} {m} ps ops p oep = opps where
>   opps : OptPolicySeq (p :: ps)
>   opps (p' :: ps') x r v = transitiveLTE (val x r v (p' :: ps')) 
>                                          (val x r v (p' :: ps)) 
>                                          (val x r v (p :: ps)) 
>                                          s3 s4 where
>     gy' : GoodCtrl t x m
>     gy' = p' x r v                       
>     y'  : Ctrl t x
>     y'  = ctrl gy'
>     x' : State (S t)
>     x' = next t x y'
>     r' : Reachable x'
>     r' = reachableSpec1 x r y'
>     v' : Viable m x'
>     v' = viable {y = y'} gy'
>     s1 : (val x' r' v' ps') `LTE` (val x' r' v' ps)
>     s1 = ops ps' x' r' v'
>     s2 : (reward t x y' x' `plus` val x' r' v' ps') `LTE` (reward t x y' x' `plus` val x' r' v' ps)
>     s2 = monotonePlusLTE (reflexiveLTE (reward t x y' x')) s1
>     s3 : (val x r v (p' :: ps')) `LTE` (val x r v (p' :: ps))
>     s3 = s2
>     s4 : (val x r v (p' :: ps)) `LTE` (val x r v (p :: ps))
>     s4 = oep p' x r v


> |||
> optExtLemma : {t : Nat} -> {n : Nat} -> 
>               (ps : PolicySeq (S t) n) -> OptExt ps (optExt ps)
> optExtLemma {t} {n} ps p' x r v = s2 where
>   p     :  Policy t (S n)
>   p     =  optExt ps
>   gy    :  GoodCtrl t x n
>   gy    =  p x r v
>   y     :  Ctrl t x
>   y     =  ctrl gy
>   x'    :  State (S t)
>   x'    =  next t x y
>   r'    :  Reachable x'
>   r'    =  reachableSpec1 x r y
>   v'    :  Viable n x'
>   v'    =  viable {y = y} gy
>   gy'   :  GoodCtrl t x n
>   gy'   =  p' x r v
>   y'    :  Ctrl t x
>   y'    =  ctrl gy'
>   x''   :  State (S t)
>   x''   =  next t x y'
>   r''   :  Reachable x''
>   r''   =  reachableSpec1 x r y'
>   v''   :  Viable n (next t x y')
>   v''   =  viable {y = y'} gy'
>   g     :  GoodCtrl t x n -> Val
>   g     =  cval x r v ps
>   s1    :  (g gy') `LTE` (max x v g)
>   s1    =  maxSpec x v g gy'
>   s2    :  (g gy') `LTE` (g (argmax x v g))
>   s2    =  replace {P = \ z => (g gy' `LTE` z)} (argmaxSpec x v g) s1
>   -- the rest of the steps are for the (sort of) human reader
>   s3    :  (g gy') `LTE` (g gy)
>   s3    =  s2
>   s4    :  (cval x r v ps gy') `LTE` (cval x r v ps gy)
>   s4    =  s3
>   s5    :  (reward t x y' x'' `plus` val x'' r'' v'' ps) `LTE` (reward t x y x' `plus` val x' r' v' ps)
>   s5    =  s4
>   s6    :  (val x r v (p' :: ps)) `LTE` (val x r v (p :: ps))
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
