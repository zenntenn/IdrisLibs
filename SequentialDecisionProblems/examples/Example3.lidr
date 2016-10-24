> module SequentialDecisionProblems.examples.Main

> import Decidable.Order

> import Data.Fin
> import Data.Vect
> import Data.List
> import Data.List.Quantifiers
> import Data.So
> import Control.Isomorphism
> import Effects
> import Effect.Exception
> import Effect.StdIO
> import Syntax.PreorderReasoning

> import SequentialDecisionProblems.CoreTheory
> import SequentialDecisionProblems.FullTheory
> import SequentialDecisionProblems.Utils
> import SequentialDecisionProblems.Helpers

> import List.Operations
> import List.Properties
> import BoundedNat.BoundedNat
> import BoundedNat.Operations
> import BoundedNat.Properties
> import SequentialDecisionProblems.examples.LeftAheadRight
> import Sigma.Sigma
> import Sigma.Operations
> import Sigma.Properties
> import Nat.OperationsProperties
> import Nat.LTEProperties
> import Nat.LTProperties
> import Finite.Predicates
> import Finite.Operations
> import Finite.Properties
> import Unique.Predicates
> import Decidable.Predicates
> import Unit.Properties
> import Void.Properties
> import Opt.Operations
> import Rel.TotalPreorder
> import LocalEffect.Exception
> import LocalEffect.StdIO
> import Fin.Operations
> import Pairs.Operations

> -- %default total
> %auto_implicits off

> -- %logging 5

Like "Example2.lidr", but now |step t x y| is empty in states
corresponding to |maxColumn|, no matter which |y| is selected! Thus,
such states are not viable for more than zero steps. Attemps at making
more than zero decision steps starting from |maxColumn| should be
detected and rejected.


* The monad M (List):

** M is a monad:

> SequentialDecisionProblems.CoreTheory.M = List
> SequentialDecisionProblems.CoreTheory.fmap = List.Operations.fmap

> SequentialDecisionProblems.Utils.ret = List.Operations.ret
> SequentialDecisionProblems.Utils.bind = List.Operations.bind

** M is a container monad:

> SequentialDecisionProblems.CoreTheory.Elem = Data.List.Elem
> SequentialDecisionProblems.CoreTheory.NotEmpty = List.Operations.NonEmpty
> SequentialDecisionProblems.CoreTheory.All = Data.List.Quantifiers.All
> SequentialDecisionProblems.CoreTheory.elemNotEmptySpec0 = List.Properties.elemNonEmptySpec0
> SequentialDecisionProblems.CoreTheory.elemNotEmptySpec1 = List.Properties.elemNonEmptySpec1
> SequentialDecisionProblems.CoreTheory.tagElem = List.Operations.tagElem
> SequentialDecisionProblems.CoreTheory.allElemSpec0 = List.Properties.containerMonadSpec3


* The decision process:

> maxColumn : Nat
> maxColumn = 10

> nColumns : Nat
> nColumns = S maxColumn

** States:

> SequentialDecisionProblems.CoreTheory.State t = LTB nColumns

** Controls:

> SequentialDecisionProblems.CoreTheory.Ctrl t x = LeftAheadRight

** Transition function:

> SequentialDecisionProblems.CoreTheory.nexts t (MkSigma Z prf) Left =
>   [MkSigma maxColumn (ltIdS maxColumn)]
> SequentialDecisionProblems.CoreTheory.nexts t (MkSigma (S n) prf) Left with (decLT (S n) maxColumn)
>   | (Yes p)     = [MkSigma n (ltLemma1 n nColumns prf)]
>   | (No contra) = []
> SequentialDecisionProblems.CoreTheory.nexts t (MkSigma n prf) Ahead with (decLT n maxColumn)
>   | (Yes p)     = [MkSigma n prf]
>   | (No contra) = []
> SequentialDecisionProblems.CoreTheory.nexts t (MkSigma n prf) Right with (decLT n maxColumn)
>   | (Yes p)     = [MkSigma (S n) (LTESucc p)]
>   | (No contra) = []

> nextsLemma0 : {t : Nat} -> 
>               (x : State t) -> (outl x `LT` maxColumn) -> nexts t x Ahead = [x]
> nextsLemma0 {t} (MkSigma i prf) p with (decLT i maxColumn)
>   | (Yes _) = Refl
>   | (No contra) = void (contra p)

> nextsLemma1 : {t : Nat} -> 
>               (x : State t) -> (outl x `LT` maxColumn) -> 
>               SequentialDecisionProblems.CoreTheory.NotEmpty (nexts t x Ahead)
> nextsLemma1 {t} x prf with (decLT (outl x) maxColumn)
>   | (Yes p) = s3 where
>     s1 : SequentialDecisionProblems.CoreTheory.NotEmpty [x] 
>     s1 = SequentialDecisionProblems.CoreTheory.elemNotEmptySpec0 x [x] Here
>     s2 : [x] = nexts t x Ahead
>     s2 = sym (nextsLemma0 x p)
>     s3 : SequentialDecisionProblems.CoreTheory.NotEmpty (nexts t x Ahead)
>     s3 = replace s2 s1
>   | (No contra) = void (contra prf)

** Reward function:

> SequentialDecisionProblems.CoreTheory.Val = Nat

> SequentialDecisionProblems.CoreTheory.reward t x y (MkSigma c _) =
>   if c == Z
>   then (S Z)
>   else if (S c) == nColumns
>        then (S (S Z))
>        else Z

> SequentialDecisionProblems.CoreTheory.plus = Prelude.Nat.plus
> SequentialDecisionProblems.CoreTheory.zero = Z

> SequentialDecisionProblems.CoreTheory.LTE = Prelude.Nat.LTE
> SequentialDecisionProblems.FullTheory.reflexiveLTE = Nat.LTEProperties.reflexiveLTE
> SequentialDecisionProblems.FullTheory.transitiveLTE = Nat.LTEProperties.transitiveLTE
> SequentialDecisionProblems.FullTheory.monotonePlusLTE = Nat.LTEProperties.monotoneNatPlusLTE

** M is measurable:

> SequentialDecisionProblems.CoreTheory.meas = sum
> SequentialDecisionProblems.FullTheory.measMon = sumMon

* Viable and Reachable

> -- Viable : (n : Nat) -> State t -> Type
> SequentialDecisionProblems.CoreTheory.Viable  Z    _ = Unit
> SequentialDecisionProblems.CoreTheory.Viable (S n) x with (decLT (outl x) maxColumn)
>   | (Yes _) = Unit
>   | (No  _) = Void

> viableLemma0 : {t : Nat} -> {x : State t} -> Viable Z x = Unit
> viableLemma0 = Refl

> viableLemma1 : {t : Nat} -> {n : Nat} -> {x : State t} -> 
>                (outl x) `Prelude.Nat.LT` maxColumn -> Viable (S n) x = Unit
> viableLemma1 {t} {n} {x} prf with (decLT (outl x) maxColumn)
>   | (Yes _) = Refl
>   | (No contra) = void (contra prf)

> viableLemma2 : {t : Nat} -> {n : Nat} -> {x : State t} -> 
>                Not ((outl x) `Prelude.Nat.LT` maxColumn) -> Viable (S n) x = Void
> viableLemma2 {t} {n} {x} prf with (decLT (outl x) maxColumn)
>   | (Yes p) = void (prf p)
>   | (No _) = Refl

> viableLemma : {t : Nat} -> {n : Nat} ->
>               (x : State t) -> 
>               SequentialDecisionProblems.CoreTheory.All (Viable {t = S t} n) (nexts t x Ahead)
> viableLemma {t} {n = Z} (MkSigma i prf) with (decLT i maxColumn)
>   | (Yes p) = res where
>     res : SequentialDecisionProblems.CoreTheory.All (Viable {t = S t} Z) [MkSigma i prf]
>     res = v :: Nil where
>       v : Viable {t = S t} Z (MkSigma i prf)
>       v with (decLT i maxColumn)
>         | (Yes _) = MkUnit
>         | (No  contra) = void (contra p)
>   | (No  _) = Nil
> viableLemma {t} {n = S m} (MkSigma i prf) with (decLT i maxColumn)
>   | (Yes p) = res where
>     res : SequentialDecisionProblems.CoreTheory.All (Viable {t = S t} (S m)) [MkSigma i prf]
>     res = v :: Nil where
>       v : Viable {t = S t} (S m) (MkSigma i prf)
>       v with (decLT i maxColumn)
>         | (Yes _) = MkUnit
>         | (No  contra) = void (contra p)
>   | (No  _) = Nil

> -- viableSpec1 : (x : State t) -> Viable (S n) x -> GoodCtrl t x n
> SequentialDecisionProblems.CoreTheory.viableSpec1 {t} {n} x v with (decLT (outl x) maxColumn)
>   | (Yes prf) = MkSigma Ahead (ne, av) where
>     ne : NotEmpty (nexts t x Ahead)
>     ne = nextsLemma1 x prf
>     av : SequentialDecisionProblems.CoreTheory.All (Viable {t = S t} n) (nexts t x Ahead)
>     av = viableLemma x 
>   | (No _) = void v

> -- Reachable : State t' -> Type
> SequentialDecisionProblems.CoreTheory.Reachable x' = Unit

> -- reachableSpec1 : (x : State t) -> Reachable {t' = t} x -> (y : Ctrl t x) -> All (Reachable {t' = S t}) (nexts t x y)
> SequentialDecisionProblems.CoreTheory.reachableSpec1 {t} x r y = all (nexts t x y) where
>   all : (xs : List (State (S t))) -> SequentialDecisionProblems.CoreTheory.All (Reachable {t' = S t}) xs
>   all Nil = Nil
>   all (x :: xs) = MkUnit :: (all xs)


* |cvalargmax| and |cvalmax| 

We want to implement |cvalmax|, |cvalargmax|, |cvalmaxSpec| and |cvalargmaxSpec|. This
can be easily done in terms of |Opt.max| and |Opt.argmax| if we can show
that 

1) |LTE| is a *total* preorder 

2) |GoodCtrl t x n| is finite and, for every |t : Nat|, |x : State t|
   such that |Viable (S n) x|, its cardinality is not zero.

The first condition trivially holds 

> totalPreorderLTE : TotalPreorder Val
> totalPreorderLTE = MkTotalPreorder SequentialDecisionProblems.CoreTheory.LTE
>                                    Nat.LTEProperties.reflexiveLTE 
>                                    Nat.LTEProperties.transitiveLTE 
>                                    Nat.LTEProperties.totalLTE

Finiteness and non-zero cardinality of |GoodCtrl t x n|

< finiteGoodCtrl : {t : Nat} -> {n : Nat} -> 
<                  (x : State t) -> 
<                  Finite (GoodCtrl t x n) 

and

< cnzGoodCtrl : {t : Nat} -> {n : Nat} -> 
<               (x : State t) -> (v : Viable {t = t} (S n) x) ->
<               CardNotZ (finiteGoodCtrl {t} {n} x)

follow from finiteness of |All|

> -- finiteAll : {A : Type} -> {P : A -> Type} -> 
> --             Finite1 P -> (ma : M A) -> Finite (All P ma)
> SequentialDecisionProblems.Helpers.finiteAll = List.Properties.finiteAll

, finiteness of |Viable|

> -- finiteViable : {t : Nat} -> {n : Nat} -> 
> --                (x : State t) -> Finite (Viable {t} n x)
> SequentialDecisionProblems.Helpers.finiteViable {t} {n = Z}    _ = finiteUnit
> SequentialDecisionProblems.Helpers.finiteViable {t} {n = S m} x with (decLT (outl x) maxColumn)
>   | (Yes p) = finiteUnit -- s3 where
>     -- s1 : Finite Unit
>     -- s1 = finiteUnit
>     -- s2 : Viable {t} (S m) x = Unit
>     -- s2 = viableLemma1 {t = t} {n = m} {x = x} p
>     -- s3 : Finite (Viable {t} (S m) x)
>     -- s3 = replace (sym s2) s1
>   | (No  c) = finiteVoid -- s3 where
>     -- s1 : Finite Void
>     -- s1 = finiteVoid
>     -- s2 : Viable {t} (S m) x = Void
>     -- s2 = viableLemma2 {t = t} {n = m} {x = x} c
>     -- s3 : Finite (Viable {t} (S m) x)
>     -- s3 = replace (sym s2) s1

, finiteness of |NonEmpty|

> -- finiteNonEmpty : {t : Nat} -> {n : Nat} -> 
> --                  (x : State t) -> (y : Ctrl t x) -> 
> --                  Finite (SequentialDecisionProblems.CoreTheory.NonEmpty (nexts t x y))
> SequentialDecisionProblems.Helpers.finiteNotEmpty {t} {n} x y = List.Properties.finiteNonEmpty (nexts t x y)

and, finally, finiteness of controls

> -- finiteCtrl : {t : Nat} -> {n : Nat} -> (x : State t) -> Finite (Ctrl t x) 
> SequentialDecisionProblems.Helpers.finiteCtrl _ = finiteLeftAheadRight
> %freeze SequentialDecisionProblems.Helpers.finiteCtrl

With these results in place, we have

> SequentialDecisionProblems.FullTheory.cvalmax x r v ps =
>   Opt.Operations.max totalPreorderLTE (finiteGoodCtrl x) (cardNotZGoodCtrl x v) (cval x r v ps)

> SequentialDecisionProblems.CoreTheory.cvalargmax x r v ps =
>   Opt.Operations.argmax totalPreorderLTE (finiteGoodCtrl x) (cardNotZGoodCtrl x v) (cval x r v ps)

> SequentialDecisionProblems.FullTheory.cvalmaxSpec x r v ps =
>   Opt.Operations.maxSpec totalPreorderLTE (finiteGoodCtrl x) (cardNotZGoodCtrl x v) (cval x r v ps)

> SequentialDecisionProblems.FullTheory.cvalargmaxSpec x r v ps =
>   Opt.Operations.argmaxSpec totalPreorderLTE (finiteGoodCtrl x) (cardNotZGoodCtrl x v) (cval x r v ps)


* Decidability of Viable

> dViable : {t : Nat} -> (n : Nat) -> (x : State t) -> Dec (Viable {t} n x)
> dViable {t}  Z    _ = Yes MkUnit
> dViable {t} (S n) x with (decLT (outl x) maxColumn)
>   | (Yes _) = Yes MkUnit
>   | (No  _) = No void


* The computation:

> -- showState : {t : Nat} -> State t -> String
> SequentialDecisionProblems.Utils.showState = show

> -- showControl : {t : Nat} -> {x : State t} -> Ctrl t x -> String
> SequentialDecisionProblems.Utils.showCtrl = show

> computation : { [STDIO] } Eff ()
> computation =
>   do putStr ("enter number of steps:\n")
>      nSteps <- getNat
>      putStr ("enter initial column:\n")
>      x0 <- getLTB nColumns
>      case (dViable {t = Z} nSteps x0) of
>        (Yes v0) => do putStrLn ("computing optimal policies ...")
>                       ps   <- pure (backwardsInduction Z nSteps)
>                       putStrLn ("computing optimal controls ...")
>                       mxys <- pure (possibleStateCtrlSeqs x0 () v0 ps)
>                       putStrLn (show mxys)
>                       putStrLn ("done!")                       
>        (No _)   => putStrLn ("initial column non viable for " ++ cast {from = Int} (cast nSteps) ++ " steps")

> main : IO ()
> main = run computation


> {-

> ---}

-- Local Variables:
-- idris-packages: ("effects")
-- End:
