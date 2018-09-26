> module SequentialDecisionProblems.TabBackwardsInduction2

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

In this case, we can implement a "tabulated" versions of |backwardsInduction| 

< backwardsInduction : (t : Nat) -> (n : Nat) -> PolicySeq t n
< backwardsInduction t  Z     =  Nil
< backwardsInduction t (S n)  =  let ps = backwardsInduction (S t) n in
<                                optExt ps :: ps

which is linear in the number of decidion steps. The idea is to
implement a function that returns two tables: one representing a
sequence of policies and the other one representing their value:

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
> ValueTable : Nat -> Nat -> Type
> ValueTable t n = Vect (cardReachableAndViableState t n) Val

< tabBackwardsInduction : (t : Nat) -> (n : Nat) -> (PolicyTableSeq t n, ValueTable t n)

For zero backwards induction steps, we simply return the empty sequence
and a vector of zero values:

< tabBackwardsInduction t  Z     =  (Nil, zeroVec (cardReachableAndViableState t Z))

where

> zeroVec : (n : Nat) -> Vect n Val
> zeroVec Z     = Nil
> zeroVec (S n) = zero :: zeroVec n

For one or more backwards induction steps, we invoke a tabulated version of |optExt|

< tabBackwardsInduction t (S n)  =  let (pts, vt) = tabBackwardsInduction (S t) n in
<                                   let (pt, vt') = tabOptExt vt in
<                                   (pt :: pts, vt')

Here

> |||
> tabOptExt : {t, n : Nat} -> 
>             (vt : ValueTable (S t) n) -> 
>             (PolicyTable t (S n), ValueTable t (S n))

We implement |tabOptExt| on the basis of the implementation of |optExt|
of the core theory. We start with a tabulated version of |sval|:

> tabSval : {t,n : Nat} -> 
>           (x  : State t) -> .(r  : Reachable x) -> .(v  : Viable (S n) x) ->
>           (gy  : GoodCtrl t x n) -> 
>           (vt : Vect (cardReachableAndViableState (S t) n) Val) ->
>           PossibleNextState x (ctrl gy) -> Val
> tabSval {t} {n} x r v gy vt (MkSigma x' x'emx') =
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

> tabCval : {t, n : Nat} -> 
>           (x  : State t) -> .(r  : Reachable x) -> .(v  : Viable (S n) x) ->
>           (vt : Vect (cardReachableAndViableState (S t) n) Val) -> 
>           GoodCtrl t x n -> Val
> tabCval {t} x r v vt gy = let y    : Ctrl t x
>                                    = ctrl gy in
>                           let mx'  : M (State (S t))
>                                    = nexts t x y in
>                           meas (fmap (tabSval x r v gy vt) (tagElem mx'))

> tabCvalargmaxMax : {t, n : Nat} -> 
>                    (x  : State t) -> .(r : Reachable x) -> .(v : Viable (S n) x) ->
>                    (vt : Vect (cardReachableAndViableState (S t) n) Val) -> (GoodCtrl t x n, Val)

> tabCvalargmax : {t, n : Nat} -> 
>                 (x  : State t) -> .(r : Reachable x) -> .(v : Viable (S n) x) ->
>                 (vt : Vect (cardReachableAndViableState (S t) n) Val) -> GoodCtrl t x n

< tabOptExt : {t, n : Nat} -> 
<             (vt : ValueTable (S t) n) -> 
<             (PolicyTable t (S n), ValueTable t (S n))

< vectReachableAndViableState : (t : Nat) -> (n : Nat) -> 
<                               Vect (cardReachableAndViableState t n) (Sigma (State t) (ReachableAndViable n))

> {-
> tabOptExt {t} {n} vt = 
>   let xrv  -- : ((k : Fin (cardReachableAndViableState t (S n))) -> Sigma (State t) (ReachableAndViable (S n)))
>            = \ k => index k (vectReachableAndViableState t (S n)) in
>   let x    : ((k : Fin (cardReachableAndViableState t (S n))) -> State t)
>            = \ k => outl (xrv k) in
>   let rv   -- : ((k : Fin (cardReachableAndViableState t (S n))) -> ReachableAndViable (S n) (x k))
>            = \ k => outr (xrv k) in
>   let gy   -- : ((k : Fin (cardReachableAndViableState t (S n))) -> GoodCtrl t (x k) n)
>            = \ k => tabCvalargmax (x k) (fst (rv k)) (snd (rv k)) vt in
>   let ptf  -- : ((k : Fin (cardReachableAndViableState t (S n))) -> (Sigma (State t) (\ x => (ReachableAndViable (S n) x, GoodCtrl t x n))))
>            -- = \ k => MkSigma (x k) (rv k, fst (gyv k)) in
>            = \ k => MkSigma (x k) (rv k, gy k) in
>   let vtf' : ((k : Fin (cardReachableAndViableState t (S n))) -> Val)
>            = \ k => tabCval (x k) (fst (rv k)) (snd (rv k)) vt (gy k) in -- \ k => snd (gyv k) in
>   let pt   : PolicyTable t (S n)
>            = toVect ptf in
>   let vt'  : ValueTable t (S n)
>            = toVect vtf' in
>   (pt, vt') 
> ---}
> --{-
> tabOptExt {t} {n} vt = 
>   let xrv   : ((k : Fin (cardReachableAndViableState t (S n))) -> 
>                Sigma (State t) (ReachableAndViable {t = t} (S n)))
>             = \ k => index k (vectReachableAndViableState t (S n)) in
>   let x     : ((k : Fin (cardReachableAndViableState t (S n))) -> State t)
>             = \ k => outl (xrv k) in
>   let rv    : ((k : Fin (cardReachableAndViableState t (S n))) -> ReachableAndViable {t = t} (S n) (x k))
>             = \ k => outr (xrv k) in
>   let gy    : ((k : Fin (cardReachableAndViableState t (S n))) -> GoodCtrl t (x k) n)
>             = \ k => tabCvalargmax {t = t} {n = n} (x k) (Prelude.Basics.fst (rv k)) (Prelude.Basics.snd (rv k)) vt in
>   let ptf   : ((k : Fin (cardReachableAndViableState t (S n))) -> 
>                (Sigma (State t) (\ x => (ReachableAndViable {t = t} (S n) x, GoodCtrl t x n))))
>             = \ k => MkSigma (x k) (rv k, gy k) in
>   let pt    : PolicyTable t (S n)
>             = toVect ptf in
>   let xrvgy : ((k : Fin (cardReachableAndViableState t (S n))) -> 
>                Sigma (State t) (\ x => (ReachableAndViable {t = t} (S n) x, GoodCtrl t x n)))
>             = \ k => index k pt in
>   let x'    : ((k : Fin (cardReachableAndViableState t (S n))) -> State t)
>             = \ k => outl (xrvgy k) in
>   let rv'   : ((k : Fin (cardReachableAndViableState t (S n))) -> ReachableAndViable {t = t} (S n) (x' k))
>             = \ k => Prelude.Basics.fst (outr (xrvgy k)) in
>   let gy'   : ((k : Fin (cardReachableAndViableState t (S n))) -> GoodCtrl t (x' k) n)
>             = \ k => Prelude.Basics.snd (outr (xrvgy k)) in                    
>   let vtf'  : ((k : Fin (cardReachableAndViableState t (S n))) -> Val)
>             -- = \ k => tabCval (x k) (Prelude.Basics.fst (rv k)) (Prelude.Basics.snd (rv k)) vt (gy k) in
>             = \ k => tabCval (x' k) (Prelude.Basics.fst (rv' k)) (Prelude.Basics.snd (rv' k)) vt (gy' k) in
>   let vt'   : ValueTable t (S n)
>             = toVect vtf' in
>   (pt, vt') 
> ---}

With |tabOptExt| in place, the full implementation of tabulated
backwards induction is

> {-

> |||
> tabBackwardsInduction : (t : Nat) -> (n : Nat) -> (PolicyTableSeq t n, ValueTable t n)
> tabBackwardsInduction t  Z     =  (Nil, zeroVec (cardReachableAndViableState t Z))
> tabBackwardsInduction t (S n)  =  let (pts, vt) = tabBackwardsInduction (S t) n in
>                                   let (pt, vt') = tabOptExt vt in
>                                   (pt :: pts, vt')

> ---}

> --{-

> |||
> tabBackwardsInduction' : (t : Nat) -> (n : Nat) -> (PolicyTableSeq t n, ValueTable t n)
> tabBackwardsInduction' t  Z     =  (Nil, zeroVec (cardReachableAndViableState t Z))
> tabBackwardsInduction' t (S n)  =  let (pts, vt) = tabBackwardsInduction' (S t) n in
>                                    let (pt, vt') = tabOptExt vt in
>                                    (pt :: pts, vt')

> tabOptExt' : {t, n : Nat} -> 
>              (vt : ValueTable (S t) n) -> 
>              PolicyTable t (S n)
> tabOptExt' {t} {n} vt = 
>   let xrv  -- : ((k : Fin (cardReachableAndViableState t (S n))) -> Sigma (State t) (ReachableAndViable (S n)))
>            = \ k => index k (vectReachableAndViableState t (S n)) in
>   let x    : ((k : Fin (cardReachableAndViableState t (S n))) -> State t)
>            = \ k => outl (xrv k) in
>   let rv   -- : ((k : Fin (cardReachableAndViableState t (S n))) -> ReachableAndViable (S n) (x k))
>            = \ k => outr (xrv k) in
>   let gy   -- : ((k : Fin (cardReachableAndViableState t (S n))) -> GoodCtrl t (x k) n)
>            = \ k => tabCvalargmax (x k) (fst (rv k)) (snd (rv k)) vt in
>   let ptf  -- : ((k : Fin (cardReachableAndViableState t (S n))) -> (Sigma (State t) (\ x => (ReachableAndViable (S n) x, GoodCtrl t x n))))
>            = \ k => MkSigma (x k) (rv k, gy k) in
>   let pt   : PolicyTable t (S n)
>            = toVect ptf in
>   pt


> |||
> tabBackwardsInduction : (t : Nat) -> (n : Nat) -> PolicyTableSeq t n
> tabBackwardsInduction t  Z     =  Nil
> tabBackwardsInduction t (S n)  =  let (pts, vt) = tabBackwardsInduction' (S t) n in
>                                   let pt        = tabOptExt' vt in
>                                   pt :: pts
                                   
> ---}


> {-

> ---}
