> module SequentialDecisionProblems.TabBackwardsInduction1

> import Data.Vect
> import Control.Isomorphism
> import Debug.Trace

> import SequentialDecisionProblems.CoreTheory
> import SequentialDecisionProblems.Utils

> import Nat.Operations
> import Nat.OperationsProperties
> import Nat.LTEProperties
> import Finite.Predicates
> import Finite.Operations
> import Finite.Properties
> import Decidable.Properties
> import Sigma.Sigma
> import Sigma.Operations
> import Pairs.Operations
> import Vect.Operations
> import Vect.Properties
> import Decidable.Predicates
> import Fin.Operations

> %default total
> %access public export
> -- %access export
> %auto_implicits off


* Tabulation

If the state space is finite

> finiteState : (t : Nat) -> Finite (State t)

, we can compute the number of values of type |State t| and collect them
in a vector

> cardState : (t : Nat) -> Nat
> cardState t = card (finiteState t)

> vectState : (t : Nat) -> Vect (cardState t) (State t)
> vectState t = toVect (finiteState t)

If |Reachable| and |Viable n| are also decidable

> decidableReachable : {t' : Nat} -> (x' : State t') -> Dec (Reachable x')

< decidableViable : {t : Nat} -> (n : Nat) -> (x : State t) -> Dec (Viable n x)

then their conjunction

> ReachableAndViable : {t : Nat} -> (n : Nat) -> (x : State t) -> Type
> ReachableAndViable n x = (Reachable x , Viable n x)

is decidable

> decidableReachableAndViable : {t : Nat} -> (n : Nat) -> (x : State t) -> Dec (ReachableAndViable n x)
> decidableReachableAndViable n x = decPair (decidableReachable x) (decidableViable n x)

and we can collect all states which are reachable and viable in a vector:

> cardReachableAndViableState : (t : Nat) -> (n : Nat) -> Nat
> cardReachableAndViableState t n = outl (f t n) where
>   f : (t : Nat) -> (n : Nat) -> Sigma Nat (\ m => Vect m (Sigma (State t) (ReachableAndViable n)))
>   f t n = filterTagSigma (decidableReachableAndViable n) (vectState t)

> vectReachableAndViableState : (t : Nat) -> (n : Nat) -> 
>                               Vect (cardReachableAndViableState t n) (Sigma (State t) (ReachableAndViable n))
> vectReachableAndViableState t n = outr (f t n) where
>   f : (t : Nat) -> (n : Nat) -> Sigma Nat (\ m => Vect m (Sigma (State t) (ReachableAndViable n)))
>   f t n = filterTagSigma (decidableReachableAndViable n) (vectState t)

In this case, we can implement a "tabulated" versions of |bi| which is
linear in the number of decidion steps. Remember that |optExt| takes a
policy sequence for |n| steps and computes a policy sequence for |n + 1|
steps:

< optExt : {t, n : Nat} -> 
<          (ps : PolicySeq (S t) n) -> Policy t (S n)

The idea is to replace the |ps| argument of |optExt| with a "value
table" |vt : Vect (cardReachableAndViableState t n) Val| storing the
value, for every state in |vectReachableAndViableState (S t) n|, of
taking |n| decision steps with |ps| starting from that state. Also ...


> |||
> PolicyTable : (t : Nat) -> (n : Nat) -> Type
> PolicyTable t  Z    = Unit
> PolicyTable t (S m) = Vect 
>                       (cardReachableAndViableState t (S m)) 
>                       (Sigma (State t) (\x => (ReachableAndViable (S m) x, GoodCtrl t x m)))

> |||
> data PolicyTableSeq : (t : Nat) -> (n : Nat) -> Type where
>   Nil   :  {t : Nat} -> 
>            PolicyTableSeq t Z
>   (::)  :  {t, n : Nat} -> 
>            PolicyTable t (S n) -> PolicyTableSeq (S t) n -> PolicyTableSeq t (S n)

> |||
> toptExt : {t, n : Nat} -> 
>           (vt : Vect (cardReachableAndViableState (S t) n) Val) -> PolicyTable t (S n)

We implement |toptExt| on the basis of the implementation of |optExt|
of the core theory. We start with a tabulated version of |sval|:

> tsval : {t,n : Nat} -> 
>         (x  : State t) -> .(r  : Reachable x) -> .(v  : Viable (S n) x) ->
>         (gy  : GoodCtrl t x n) -> 
>         (vt : Vect (cardReachableAndViableState (S t) n) Val) ->
>         PossibleNextState x (ctrl gy) -> Val
> tsval {t} {n} x r v gy vt (MkSigma x' x'emx') =
>   let y    : Ctrl t x
>            = ctrl gy in
>   let mx'  : M (State (S t))
>            = nexts t x y in
>   let ar'  : All Reachable mx'
>            = reachableSpec1 x r y in
>   let av'  : All (Viable n) mx'
>            = allViable gy in
>   let r'   : Reachable x'
>            = allElemSpec0 x' mx' ar' x'emx' in
>   let v'   : Viable n x'
>            = allElemSpec0 x' mx' av' x'emx' in
>   let rvxs : Vect (cardReachableAndViableState (S t) n) (State (S t))
>            = map outl (vectReachableAndViableState (S t) n) in
>   let dRV  : ((x' : State (S t)) -> Dec (ReachableAndViable n x'))
>            = decidableReachableAndViable n in
>   let prf  : Elem x' (vectState (S t))
>            = toVectComplete (finiteState (S t)) x' in
>   let prf' : Elem x' rvxs
>            = filterTagSigmaLemma {P = ReachableAndViable n} dRV x' (vectState (S t)) prf (r',v') in
>   let k    : Fin (cardReachableAndViableState (S t) n)
>            = trace ("Lookup " ++ show n) (lookup x' rvxs prf') in
>   reward t x y x' `plus` index k vt

Next, we implement a tabulated version of |cval|:

> tcval : {t, n : Nat} -> 
>         (x  : State t) -> .(r  : Reachable x) -> .(v  : Viable (S n) x) ->
>         (vt : Vect (cardReachableAndViableState (S t) n) Val) -> 
>         GoodCtrl t x n -> Val
> tcval {t} x r v vt gy = let y    : Ctrl t x
>                                  = ctrl gy in
>                         let mx'  : M (State (S t))
>                                  = nexts t x y in
>                         meas (fmap (tsval x r v gy vt) (tagElem mx'))

And finally

> tcvalargmax : {t, n : Nat} -> 
>               (x  : State t) -> .(r : Reachable x) -> .(v : Viable (S n) x) ->
>               (vt : Vect (cardReachableAndViableState (S t) n) Val) -> GoodCtrl t x n

> {-
> toptExt {t} {n} vt = pt where
>   pt : PolicyTable t (S n)
>   pt = toVect ptf where
>     ptf : Fin (cardReachableAndViableState t (S n)) -> (Sigma (State t) (\x => (ReachableAndViable (S n) x, GoodCtrl t x n)))
>     ptf k = MkSigma x (rv, gy) where
>       xrv : Sigma (State t) (ReachableAndViable (S n))
>       xrv = index k (vectReachableAndViableState t (S n))
>       x   : State t
>       x   = outl xrv
>       rv  : ReachableAndViable (S n) x
>       rv  = outr xrv
>       gy  : GoodCtrl t x n
>       gy  = tcvalargmax x (fst rv) (snd rv) vt
> -}
> toptExt {t} {n} vt = 
>   let xrv -- : ((k : Fin (cardReachableAndViableState t (S n))) -> Sigma (State t) (ReachableAndViable (S n)))
>           = \ k => index k (vectReachableAndViableState t (S n)) in
>   let x   : ((k : Fin (cardReachableAndViableState t (S n))) -> State t)
>           = \ k => outl (xrv k) in
>   let rv  -- : ((k : Fin (cardReachableAndViableState t (S n))) -> ReachableAndViable (S n) (x k))
>           = \ k => outr (xrv k) in
>   let gy  -- : ((k : Fin (cardReachableAndViableState t (S n))) -> GoodCtrl t (x k) n)
>           = \ k => tcvalargmax (x k) (fst (rv k)) (snd (rv k)) vt in
>   let ptf -- : ((k : Fin (cardReachableAndViableState t (S n))) -> (Sigma (State t) (\ x => (ReachableAndViable (S n) x, GoodCtrl t x n))))
>           = \ k => MkSigma (x k) (rv k, gy k) in
>   let pt  : PolicyTable t (S n)
>           = toVect ptf in
>   pt 

* Tabulated tail-recursive backwards induction

With |toptExt| in place, it is easy to implement a tabulated version of
|trbi|:

> ||| A table of the result of calling |flip val| (roughly) on a policy sequence
> ValueTable : Nat -> Nat -> Type
> ValueTable t n = Vect (cardReachableAndViableState t n) Val

> |||
> PolicySeqAndTab : Nat -> Nat -> Type
> PolicySeqAndTab t n = (PolicySeq t n, ValueTable t n)

> |||
> zeroVec : (n : Nat) -> Vect n Val
> zeroVec Z     = Nil
> zeroVec (S n) = zero :: zeroVec n

> ||| Tabulated tail-recursive backwards induction iteration
> ttrbii : (t : Nat) -> (n : Nat) -> (c : Nat) -> (LTE c n) ->
>          PolicyTableSeq (c + t) (n - c) ->
>          (vt : Vect (cardReachableAndViableState (c + t) (n - c)) Val) ->
>          PolicyTableSeq t n
> 
> ttrbii t n  Z     prf pts vt = replace {P = \ z => PolicyTableSeq t z} (minusZeroRight n) pts
> {-
> ttrbii t n (S c') prf pts vt = ttrbii t n c' prf' pts' vt'' where
>   bic  : S (n - S c') = n - c'
>   bic  = minusLemma4 prf
>   prf' : LTE c' n
>   prf' = lteLemma1 c' n prf
>   pt   : PolicyTable (c' + t) (S (n - S c'))
>   pt   = toptExt vt
>   pts' : PolicyTableSeq (c' + t) (n - c')
>   pts' = replace {P = \ z => PolicyTableSeq (c' + t) z} bic (pt :: pts)
>   vt'  : Vect (cardReachableAndViableState (c' + t) (S (n - S c'))) Val
>   vt'  = toVect vt'f where
>     vt'f : Fin (cardReachableAndViableState (c' + t) (S (n - S c'))) -> Val
>     vt'f k = tcval x r v vt gy where
>       xrvgy : Sigma (State (c' + t)) (\ x => (ReachableAndViable (S (n - S c')) x, GoodCtrl (c' + t) x (n - S c')))
>       xrvgy = index k pt
>       x     : State (c' + t)
>       x     = outl xrvgy
>       rv    : ReachableAndViable (S (n - S c')) x
>       rv    = fst (outr xrvgy)
>       r     : Reachable x
>       r     = fst rv
>       v     : Viable (S (n - S c')) x
>       v     = snd rv
>       gy    : GoodCtrl (c' + t) x (n - S c')
>       gy    = snd (outr xrvgy)
>   vt''  : Vect (cardReachableAndViableState (c' + t) (n - c')) Val
>   vt''  = replace {P = \z => Vect (cardReachableAndViableState (c' + t) z) Val} bic vt'
> -}
> ttrbii t n (S c') prf pts vt = 
>   let bic   : (S (n - S c') = n - c')
>             = minusLemma4 prf in
>   let prf'  : LTE c' n
>             = lteLemma1 c' n prf in
>   let pt    : PolicyTable (c' + t) (S (n - S c'))
>             = toptExt vt in
>   let pts'  : PolicyTableSeq (c' + t) (n - c')
>             = replace {P = \ z => PolicyTableSeq (c' + t) z} bic (pt :: pts) in
>   let xrvgy -- : ((k : Fin (cardReachableAndViableState (c' + t) (S (n - S c')))) -> 
>             --    Sigma (State (c' + t)) (\ x => (ReachableAndViable (S (n - S c')) x, GoodCtrl (c' + t) x (n - S c'))))
>             = \ k => index k pt in
>   let x     : ((k : Fin (cardReachableAndViableState (c' + t) (S (n - S c')))) -> State (c' + t))
>             = \ k => outl (xrvgy k) in
>   let rv    -- : ((k : Fin (cardReachableAndViableState (c' + t) (S (n - S c')))) -> ReachableAndViable (S (n - S c')) (x k))
>             = \ k => fst (outr (xrvgy k)) in
>   let r     : ((k : Fin (cardReachableAndViableState (c' + t) (S (n - S c')))) -> Reachable {t' = c' + t} (x k))
>             = \ k => fst (rv k) in
>   let v     : ((k : Fin (cardReachableAndViableState (c' + t) (S (n - S c')))) -> Viable {t = c' + t} (S (n - S c')) (x k))
>             = \ k => snd (rv k) in
>   let gy    : ((k : Fin (cardReachableAndViableState (c' + t) (S (n - S c')))) -> GoodCtrl (c' + t) (x k) (n - S c'))
>             = \ k => snd (outr (xrvgy k)) in          
>   let vt'f  : ((k : Fin (cardReachableAndViableState (c' + t) (S (n - S c')))) -> Val)
>             = \ k => tcval (x k) (r k) (v k) vt (gy k) in
>   let vt'   : Vect (cardReachableAndViableState (c' + t) (S (n - S c'))) Val
>             = toVect vt'f in
>   let vt''  : Vect (cardReachableAndViableState (c' + t) (n - c')) Val
>             = replace {P = \z => Vect (cardReachableAndViableState (c' + t) z) Val} bic vt' in
>   ttrbii t n c' prf' pts' vt'' 

> ||| Tabulated tail-recursive backwards induction
> tabTailRecursiveBackwardsInduction1 : (t : Nat) -> (n : Nat) -> PolicyTableSeq t n
> tabTailRecursiveBackwardsInduction1 t n = ttrbii t n n (reflexiveLTE n) zps (zeroVec _) where
>   zps : PolicyTableSeq (n + t) (n - n)
>   zps = replace {P = \ z => PolicyTableSeq (n + t) z} (minusZeroN n) Nil

> {-

> ---}
