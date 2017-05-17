> module SequentialDecisionProblems.TabBackwardsInduction

> import Data.Vect

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
> import Vect.Operations
> import Vect.Properties
> import Decidable.Predicates
> import Fin.Operations

> %default total
> %access public export
> %auto_implicits off


* Preliminaries

The major disadvantage of the generic backwards induction implementation
of the core theory

< bi : (t : Nat) -> (n : Nat) -> PolicySeq t n
< bi t  Z     =  Nil
< bi t (S n)  =  optExt ps :: ps where
<   ps : PolicySeq (S t) n
<   ps = bi (S t) n

is that its computational cost is exponential in the number of decidion
steps. Consider, for example, |bi 0 3|

< bi 0 3
<   = { def. |bi| }
< (optExt (bi 1 2)) :: (bi 1 2)
<   = { def. |bi| }
< (optExt ((optExt (bi 2 1)) :: (bi 2 1))) :: (optExt (bi 2 1)) :: (bi 2 1)
<   = { def. |bi| }
< (optExt ((optExt ((optExt (bi 3 0)) :: (bi 3 0))) :: (optExt (bi 3 0)) :: (bi 3 0))) :: 
< (optExt ((optExt (bi 3 0)) :: (bi 3 0))) :: 
< (optExt (bi 3 0)) :: 
< (bi 3 0)
<   = { def. |bi| }
< (optExt ((optExt ((optExt Nil) :: Nil)) :: (optExt Nil) :: Nil)) :: 
< (optExt ((optExt Nil) :: Nil)) :: 
< (optExt Nil) :: 
< Nil

resulting in

- 4 computations of |optExt Nil|
- 2 computations of |optExt ((optExt Nil) :: Nil)|
- 1 computation of |optExt ((optExt ((optExt Nil) :: Nil)) :: ((optExt Nil) :: Nil))|

or 7 calls to |optExt|. One more decision step implies 15 calls to
|optExt| suggesting that the number of calls to |optExt| for |n|
decision steps is |sum_{i = 0}^{n - 1} 2^j = (1 - 2^n) / (1 - 2)|.


* Towards a tail-recursive implementation

We can make the number of calls to |optExt| linear in |n| by rewriting
|bi| in tail-recursive form. The first step is to replace the recursive
call to |bi| with an iteration. Instead of pattern matching on the
number of steps, we delegate the computation of the policy sequence to
an auxiliary function |ibi| which implements backwards induction
iteratively:

> ||| Iterative backwards induction
> ibi : (t : Nat) -> (n : Nat) -> (c : Nat) -> LTE c n ->
>       PolicySeq (n - c + t) c -> PolicySeq t n
> ibi t n c prf ps with (n - c) proof itsEqual
>   |  Z    = replace {P = \ x => PolicySeq (Z + t) x} ceqn
>             ps where
>       ceqn : c = n
>       ceqn = minusLemma3 prf itsEqual
>   | (S m) = assert_total (ibi t n (S c) prf' ps') where
>       prf' : LTE (S c) n
>       prf' = minusLemma2 prf (sym itsEqual)
>       ps'  : PolicySeq (n - (S c) + t) (S c)
>       ps'  = replace {P = \ x => PolicySeq (x + t) (S c)} (minusLemma1 (sym itsEqual))
>              ((optExt ps) :: ps)

> ||| Tail-recursive backwardsinduction
> trbi : (t : Nat) -> (n : Nat) -> PolicySeq t n
> trbi t n = ibi t n Z LTEZero Nil

We can check that |trbi 0 3| and |bi 0 3| reduce to the same expression

< trbi 0 3
<   = { def. |trbi| }
< ibi 0 3 0 LTEZero Nil
<   = { def. |ibi| }
< ibi 0 3 1 (...) (optExt Nil) :: 
<                 Nil
<   = {def. |ibi|}
< ibi 0 3 2 (...) (optExt ((optExt Nil) :: Nil)) :: 
<                 (optExt Nil) :: 
<                 Nil
<   = {def. |ibi|}
< ibi 0 3 3 (...) (optExt ((optExt ((optExt Nil) :: Nil)) :: (optExt Nil) :: Nil)) :: 
<                 (optExt ((optExt Nil) :: Nil)) :: 
<                 (optExt Nil) :: 
<                 Nil
<   = {def. |ibi|}
< (optExt ((optExt ((optExt Nil) :: Nil)) :: (optExt Nil) :: Nil)) :: 
< (optExt ((optExt Nil) :: Nil)) :: 
< (optExt Nil) :: 
< Nil


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
taking |n| decision steps with |ps| starting from that state:

> toptExt : {t, n : Nat} -> 
>           (vt : Vect (cardReachableAndViableState (S t) n) Val) -> Policy t (S n)

We implement |toptExt| on the basis of the implementation of |optExt|
of the core theory. We start with a tabulated version of |sval|:

> tsval : {t,n : Nat} -> 
>         (x  : State t) -> .(r  : Reachable x) -> .(v  : Viable (S n) x) ->
>         (gy  : GoodCtrl t x n) -> 
>         (vt : Vect (cardReachableAndViableState (S t) n) Val) ->
>         PossibleNextState x (ctrl gy) -> Val
> tsval {t} {n} x r v gy vt (MkSigma x' x'emx') = reward t x y x' `plus` index k vt where
>   y   : Ctrl t x
>   y   = ctrl gy
>   mx' : M (State (S t))
>   mx' = nexts t x y
>   ar' : All Reachable mx'
>   ar' = reachableSpec1 x r y
>   av' : All (Viable n) mx'
>   av' = allViable gy
>   r' : Reachable x'
>   r' = allElemSpec0 x' mx' ar' x'emx'
>   v' : Viable n x'
>   v' = allElemSpec0 x' mx' av' x'emx'
>   rvxs : Vect (cardReachableAndViableState (S t) n) (State (S t))
>   rvxs = map outl (vectReachableAndViableState (S t) n)
>   k    : Fin (cardReachableAndViableState (S t) n)
>   k    = lookup x' rvxs prf' where
>     dRV : (x' : State (S t)) -> Dec (ReachableAndViable n x')
>     dRV = decidableReachableAndViable n
>     prf : Elem x' (vectState (S t))
>     prf = toVectComplete (finiteState (S t)) x'
>     prf' : Elem x' rvxs
>     prf' = filterTagSigmaLemma {P = ReachableAndViable n} dRV x' (vectState (S t)) prf (r',v')

Next, we implement a tabulated version of |cval|:

> tcval : {t, n : Nat} -> 
>         (x  : State t) -> .(r  : Reachable x) -> .(v  : Viable (S n) x) ->
>         (vt : Vect (cardReachableAndViableState (S t) n) Val) -> 
>         GoodCtrl t x n -> Val
> tcval {t} x r v vt gy = meas (fmap (tsval x r v gy vt) (tagElem mx')) where
>   y    : Ctrl t x
>   y    = ctrl gy
>   mx'  :  M (State (S t))
>   mx'  =  nexts t x y

And finally

> tcvalargmax : {t, n : Nat} -> 
>               (x  : State t) -> .(r : Reachable x) -> .(v : Viable (S n) x) ->
>               (vt : Vect (cardReachableAndViableState (S t) n) Val) -> GoodCtrl t x n

> toptExt {t} {n} vt = p where
>   p : Policy t (S n)
>   p x r v = tcvalargmax x r v vt


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
>          PolicySeq (c + t) (n - c) ->
>          (vt : Vect (cardReachableAndViableState (c + t) (n - c)) Val) ->
>          PolicySeq t n
>
> ttrbii t n  Z     prf ps vt = replace {P = \ z => PolicySeq t z} (minusZeroRight n) ps
>
> ttrbii t n (S c') prf ps vt = ttrbii t n c' prf' ps' vt'' where
>   bic  : S (n - S c') = n - c'
>   bic  = minusLemma4 prf
>   prf' : LTE c' n
>   prf' = lteLemma1 c' n prf
>   p    : Policy (c' + t) (S (n - S c'))
>   p    = toptExt vt
>   ps'  : PolicySeq (c' + t) (n - c')
>   ps'  = replace {P = \ z => PolicySeq (c' + t) z} bic (p :: ps)
>   vt'  : Vect (cardReachableAndViableState (c' + t) (S (n - S c'))) Val
>   vt'  = toVect vt'f where
>     vt'f : Fin (cardReachableAndViableState (c' + t) (S (n - S c'))) -> Val
>     vt'f k = tcval x r v vt (p x r v) where
>       xrv : Sigma (State (c' + t)) (ReachableAndViable (S (n - S c')))
>       xrv = index k (vectReachableAndViableState (c' + t) (S (n - S c')))
>       x   : State (c' + t)
>       x   = outl xrv
>       r   : Reachable {t' = c' + t} x
>       r   = fst (outr xrv)
>       v   : Viable {t = c' + t} (S (n - S c')) x
>       v   = snd (outr xrv)
>   vt''  : Vect (cardReachableAndViableState (c' + t) (n - c')) Val
>   vt''  = replace {P = \z => Vect (cardReachableAndViableState (c' + t) z) Val} bic vt'


> ||| Tabulated tail-recursive backwards induction
> tabTailRecursiveBackwardsInduction : (t : Nat) -> (n : Nat) -> PolicySeq t n
> tabTailRecursiveBackwardsInduction t n = ttrbii t n n (reflexiveLTE n) zps (zeroVec _) where
>   zps : PolicySeq (n + t) (n - n)
>   zps = replace {P = \ z => PolicySeq (n + t) z} (minusZeroN n) Nil


> {-

> ---}
