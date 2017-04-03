> module papers.JFP2016.MonadicFull

> import papers.JFP2016.MonadicCore

> import Sigma.Sigma
> import Sigma.Operations

> %default total
> %access public export
> %auto_implicits on


* |LTE|

> reflexiveLTE : (a : Val) -> a `LTE` a
> transitiveLTE : (a : Val) -> (b : Val) -> (c : Val) -> a `LTE` b -> b `LTE` c -> a `LTE` c

> monotonePlusLTE : {a, b, c, d : Val} -> a `LTE` b -> c `LTE` d -> (a `plus` c) `LTE` (b `plus` d)


* |meas|

> measMon  :  {A : Type} ->
>             (f : A -> Val) -> (g : A -> Val) ->
>             ((a : A) -> (f a) `LTE` (g a)) ->
>             (ma : M A) -> meas (fmap f ma) `LTE` meas (fmap g ma)


* |cvalargmax|

The function |cvalargmax| introduced in |CoreTheory| must deliver
optimal controls.  We need the function |cvalmax|, returning the value
of those optimal controls, in order to fully specify |cvalargmax|:

< cvalargmax      :  (x  : State t) -> (r  : Reachable x) -> (v  : Viable (S n) x) ->
<                    (ps : PolicySeq (S t) n) -> GoodCtrl t x n
                
> cvalmax         :  (x : State t) -> (r : Reachable x) -> (v : Viable (S n) x) ->
>                    (ps : PolicySeq (S t) n) -> Val
>
> cvalargmaxSpec  :  (x  : State t) -> (r  : Reachable x) -> 
>                    (v  : Viable (S n) x) ->  (ps : PolicySeq (S t) n) ->
>                    cvalmax x r v ps = cval x r v ps (cvalargmax x r v ps)
>
> cvalmaxSpec     :  (x  : State t) -> (r  : Reachable x) -> 
>                    (v  : Viable (S n) x) ->  (ps : PolicySeq (S t) n) ->
>                    (gy : GoodCtrl t x n) ->
>                    (cval x r v ps gy) `LTE` (cvalmax x r v ps)

The reason for using these very specific functions, instead of more
general |max| and |argmax|, is that optimisation is, in most case, not
computable.  The assumptions on |cvalmax| and |cvalargmax| are the
minimal requirements for the computability of optimal
extensions. Anything more general risks being non-implementable.


* The proof of correctness of |backwardsInduction|:

** Policy sequences of length zero are optimal

> nilOptPolicySeq : OptPolicySeq Nil
> nilOptPolicySeq x r v ps' = reflexiveLTE zero


** Bellman's principle of optimality:

> Bellman  :  (ps  :  PolicySeq (S t) m)  ->   OptPolicySeq ps ->
>             (p   :  Policy t (S m))     ->   OptExt ps p ->
>             OptPolicySeq (p :: ps)
>
> Bellman {t} {m} ps ops p oep = opps where
>   opps : OptPolicySeq (p :: ps)
>   opps x r v (p' :: ps') = transitiveLTE  (val x r v (p' :: ps')) 
>                                           (val x r v (p' :: ps)) 
>                                           (val x r v (p :: ps)) 
>                                           s4 s5 where
>     gy'  :  GoodCtrl t x m;;                         gy'  =  p' x r v                       
>     y'   :  Ctrl t x;;                               y'   =  ctrl gy'
>     mx'  :  M (State (S t));;                        mx'  =  nexts t x y'
>     av'  :  All (Viable m) mx';;                     av'  =  allViable gy'
>     f'   :  PossibleNextState x (ctrl gy') -> Val;;  f'   =  sval x r v gy' ps'
>     f    :  PossibleNextState x (ctrl gy') -> Val;;  f    =  sval x r v gy' ps
>     s1   :  (x' : State (S t)) -> (r' : Reachable x') -> (v' : Viable m x') ->
>             val x' r' v' ps' `LTE` val x' r' v' ps
>     s1 x' r' v' = ops x' r' v' ps' 
>     s2   :  (z : PossibleNextState x (ctrl gy')) -> (f' z) `LTE` (f z)
>     s2 (MkSigma x' x'emx') = 
>       monotonePlusLTE (reflexiveLTE (reward t x y' x')) (s1 x' r' v') where 
>         ar'  :  All Reachable mx';;  ar'  =  reachableSpec1 x r y'
>         r'   :  Reachable x';;       r'   =  allElemSpec0 x' mx' ar' x'emx'
>         v'   :  Viable m x';;        v'   =  allElemSpec0 x' mx' av' x'emx'
>     s3  :  meas (fmap f' (tagElem mx')) `LTE` meas (fmap f (tagElem mx'))
>     s3  =  measMon f' f s2 (tagElem mx')
>     s4  :  val x r v (p' :: ps') `LTE` val x r v (p' :: ps);;  s4  =  s3
>     s5  :  val x r v (p' :: ps) `LTE` val x r v (p :: ps);;    s5  =  oep x r v p'


> optExtLemma  :  (ps : PolicySeq (S t) n) -> OptExt ps (optExt ps)
> optExtLemma {t} {n} ps x r v p' = s5 where
>   p     :  Policy t (S n);;                            p    = optExt ps
>   gy    :  GoodCtrl t x n;;                            gy   = p x r v
>   y     :  Ctrl t x;;                                  y    = ctrl gy
>   av    :  All (Viable n) (nexts t x y);;              av   = allViable gy
>   gy'   :  GoodCtrl t x n;;                            gy'  = p' x r v
>   y'    :  Ctrl t x;;                                  y'   = ctrl gy'
>   av'   :  All (Viable n) (nexts t x y');;             av'  = allViable gy'
>   f     :  PossibleNextState x (ctrl gy) -> Val;;      f    = sval x r v gy ps
>   f'    :  PossibleNextState x (ctrl gy') -> Val;;     f'   = sval x r v gy' ps
>   s1    :  cval x r v ps gy' `LTE` cvalmax x r v ps;;  s1   = cvalmaxSpec x r v ps gy'
>   s2    :  cval x r v ps gy' `LTE` cval x r v ps (cvalargmax x r v ps)
>   s2    =  replace {P = \ z => (cval x r v ps gy' `LTE` z)} (cvalargmaxSpec x r v ps) s1
>   -- the rest of the steps are for the (sort of) human reader
>   s3    :  cval x r v ps gy' `LTE` cval x r v ps gy;;                                             s3 = s2
>   s4    :  meas (fmap f' (tagElem (nexts t x y'))) `LTE` meas (fmap f (tagElem (nexts t x y)));;  s4 = s3
>   s5    :  val x r v (p' :: ps) `LTE` val x r v (p :: ps);;                                       s5 = s4

** Correctness of backwards induction

> backwardsInductionLemma : (t : Nat) -> (n : Nat) -> OptPolicySeq (backwardsInduction t n)
> backwardsInductionLemma t  Z     =  nilOptPolicySeq
> backwardsInductionLemma t (S n)  =  Bellman ps ops p oep where
>   ps   : PolicySeq (S t) n;;  ps   = backwardsInduction (S t) n
>   ops  : OptPolicySeq ps;;    ops  = backwardsInductionLemma (S t) n
>   p    : Policy t (S n);;     p    = optExt ps
>   oep  : OptExt ps p;;        oep  = optExtLemma ps


> {-

> ---}

