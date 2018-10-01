> module SequentialDecisionProblems.TabBackwardsInduction2

> import Data.Vect
> import Control.Isomorphism
> -- import Debug.Trace

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

-- 

If equality on values of type |State t| is decidable

> decidableEqState : (t : Nat) -> DecEq (State t)

we can store the result of looking up the index of a reachable and
viable state in |vectReachableAndViableState t n| into a table

> iat : {t, n : Nat} -> 
>       Not (Z = cardReachableAndViableState t n) ->
>       Vect (cardState t) (Fin (cardReachableAndViableState t n)) 
> iat {t} {n} prf = toVect iatf where
>   iatf : (Fin (cardState t) -> Fin (cardReachableAndViableState t n))
>   iatf k with (lookup' (decidableEqState t) 
>                        (from (iso (finiteState t)) k) 
>                        (map outl (vectReachableAndViableState t n)))
>     | Nothing with (cardReachableAndViableState t n) proof contra
>         |   Z = void (prf Refl)
>         | S m = FZ {k = m} 
>     | Just k' = k'

The table can then be used to replace lookups (like in |tabSval|, see
below) with |index| operations. The idea is that indexing can in
principle (Blodwin feature?) be done in constant time whereas lookups
(searcing) takes liner time.

--

In this case, we can implement a "tabulated" versions of |backwardsInduction| 

< backwardsInduction : (t : Nat) -> (n : Nat) -> PolicySeq t n
< backwardsInduction t  Z     =  Nil
< backwardsInduction t (S n)  =  let ps = backwardsInduction (S t) n in
<                                optExt ps :: ps

The idea is to replace policies as functions from states to control with
policy tables. In analogy to policies as defined in the CoreTheory, the
type of a policy table that supports zero decision steps is just the
singleton type. A policy table that supports |S m| further decision
steps at decision step |t| is a vector with as many entries as there are
states in |State t| that are reachable and viable |S m| steps:

> |||
> PolicyTable : (t : Nat) -> (n : Nat) -> Type
> PolicyTable t  Z    = Unit
> PolicyTable t (S m) = Vect 
>                       (cardReachableAndViableState t (S m)) 
>                       (Sigma (State t) (\x => (ReachableAndViable (S m) x, GoodCtrl t x m)))

Similarly, sequences of policy tables are either empty or made up of a
policy table consed with a tail sequence:

> |||
> data PolicyTableSeq : (t : Nat) -> (n : Nat) -> Type where
>   Nil   :  {t : Nat} -> 
>            PolicyTableSeq t Z
>   (::)  :  {t, n : Nat} -> 
>            PolicyTable t (S n) -> PolicyTableSeq (S t) n -> PolicyTableSeq t (S n)

With these notions in place, a tabulated version of backwards induction
will be a function of type

< (t : Nat) -> (n : Nat) -> PolicyTableSeq t n

In order to implement this function, some additional notions are needed. ...

> ||| 
> ValueTable : Nat -> Nat -> Type
> ValueTable t n = Vect (cardReachableAndViableState t n) Val

> |||
> zeroVec : (n : Nat) -> Vect n Val
> zeroVec Z     = Nil
> zeroVec (S n) = zero :: zeroVec n

> |||
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
>            -- = trace ("Lookup " ++ show n) (lookup x' rvxs prf') in
>            = lookup x' rvxs prf' in
>   reward t x y x' `plus` index k vt

> |||
> tabSval' : {t,n : Nat} -> 
>            (x  : State t) -> .(r  : Reachable x) -> .(v  : Viable (S n) x) ->
>            (gy  : GoodCtrl t x n) -> 
>            (vt : Vect (cardReachableAndViableState (S t) n) Val) ->
>            Vect (cardState (S t)) (Fin (cardReachableAndViableState (S t) n)) ->
>            PossibleNextState x (ctrl gy) -> Val
> tabSval' {t} {n} x r v gy vt iat (MkSigma x' x'emx') =
>   let y    : Ctrl t x
>            = ctrl gy in
>   let k    : Fin (cardReachableAndViableState (S t) n)
>            = index (to (iso (finiteState (S t))) x') iat in
>   reward t x y x' `plus` index k vt


> |||
> tabCval : {t, n : Nat} -> 
>           (x  : State t) -> .(r  : Reachable x) -> .(v  : Viable (S n) x) ->
>           (vt : Vect (cardReachableAndViableState (S t) n) Val) -> 
>           GoodCtrl t x n -> Val
> tabCval {t} x r v vt gy = let y    : Ctrl t x
>                                    = ctrl gy in
>                           let mx'  : M (State (S t))
>                                    = nexts t x y in
>                           meas (fmap (tabSval x r v gy vt) (tagElem mx'))


> {-
> tabCval' : {t, n : Nat} -> 
>            (x  : State t) -> .(r  : Reachable x) -> .(v  : Viable (S n) x) ->
>            (vt : Vect (cardReachableAndViableState (S t) n) Val) -> 
>            Vect (cardState (S t)) (Fin (cardReachableAndViableState (S t) n)) ->
>            GoodCtrl t x n -> Val
> tabCval' {t} x r v vt iat gy = let y    : Ctrl t x
>                                         = ctrl gy in
>                                let mx'  : M (State (S t))
>                                         = nexts t x y in
>                                let tmp  : Vect (cardState (S t)) (Fin (cardReachableAndViableState (S t) n))
>                                         = iat in
>                                meas (fmap (tabSval' x r v gy vt iat) (tagElem mx'))
> -}

> |||
> tabCvalargmaxMax : {t, n : Nat} -> 
>                    (x  : State t) -> .(r : Reachable x) -> .(v : Viable (S n) x) ->
>                    (vt : Vect (cardReachableAndViableState (S t) n) Val) -> (GoodCtrl t x n, Val)

> |||
> tabCvalargmax : {t, n : Nat} -> 
>                 (x  : State t) -> .(r : Reachable x) -> .(v : Viable (S n) x) ->
>                 (vt : Vect (cardReachableAndViableState (S t) n) Val) -> GoodCtrl t x n

> |||
> tabOptExt : {t, n : Nat} -> (vt : ValueTable (S t) n) -> PolicyTable t (S n)
> tabOptExt {t} {n} vt =
>   let ptf  : ((k : Fin (cardReachableAndViableState t (S n))) -> 
>               (Sigma (State t) (\ x => (ReachableAndViable {t = t} (S n) x, GoodCtrl t x n))))
>            = \ k => let xrvk : Sigma (State t) (ReachableAndViable {t = t} (S n))
>                              = index k (vectReachableAndViableState t (S n)) in
>                     let x    : State t
>                              = outl xrvk in
>                     let rv   : ReachableAndViable {t = t} (S n) x
>                              = outr xrvk in
>                     let gy   : GoodCtrl t x n
>                              = tabCvalargmax {t = t} {n = n} x (fst rv) (snd rv) vt in
>                     MkSigma x (rv, gy) in
>   let pt   : PolicyTable t (S n)
>            = toVect ptf in
>   pt

> |||
> tabOptExt' : {t, n : Nat} -> 
>              (vt : ValueTable (S t) n) -> 
>              (PolicyTable t (S n), ValueTable t (S n))
> tabOptExt' {t} {n} vt =
>   let pt    : PolicyTable t (S n)
>             = tabOptExt vt in
>   -- let tmp   = iat {t = S t} {n = n} (believe_me 42) in
>   let vtf'  : ((k : Fin (cardReachableAndViableState t (S n))) -> Val)
>             = \ k => let ptk : Sigma (State t) (\ x => (ReachableAndViable {t = t} (S n) x, GoodCtrl t x n))
>                              = index k pt in
>                      let x   : State t
>                              = outl ptk in
>                      let rv  : ReachableAndViable {t = t} (S n) x
>                              = fst (outr ptk) in
>                      let gy  : GoodCtrl t x n
>                              = snd (outr ptk) in
>                      tabCval x (fst rv) (snd rv) vt gy in
>                      -- tabCval' x (fst rv) (snd rv) vt tmp in
>   let vt'   : ValueTable t (S n)
>             = toVect vtf' in
>   (pt, vt') 

... finally

> |||
> tabBackwardsInduction' : (t : Nat) -> (n : Nat) -> (PolicyTableSeq t n, ValueTable t n)
> tabBackwardsInduction' t  Z     =  (Nil, zeroVec (cardReachableAndViableState t Z))
> tabBackwardsInduction' t (S n)  =  let (pts, vt) = tabBackwardsInduction' (S t) n in
>                                    let (pt, vt') = tabOptExt' vt in
>                                    (pt :: pts, vt')

> |||
> tabBackwardsInduction : (t : Nat) -> (n : Nat) -> PolicyTableSeq t n
> tabBackwardsInduction t  Z     =  Nil
> tabBackwardsInduction t (S n)  =  let (pts, vt) = tabBackwardsInduction' (S t) n in
>                                   let pt        = tabOptExt vt in
>                                   pt :: pts
                                   

> {-

> ---}
