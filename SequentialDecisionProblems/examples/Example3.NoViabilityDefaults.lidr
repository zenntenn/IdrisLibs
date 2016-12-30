> module SequentialDecisionProblems.examples.Main

> import Decidable.Order

> import Data.List
> import Data.List.Quantifiers
> import Effects
> import Effect.Exception
> import Effect.StdIO

> import SequentialDecisionProblems.CoreTheory
> import SequentialDecisionProblems.FullTheory
> import SequentialDecisionProblems.Utils
> import SequentialDecisionProblems.NonDeterministicDefaults
> import SequentialDecisionProblems.OptDefaults

> import SequentialDecisionProblems.examples.LeftAheadRight

> import List.Operations
> import List.Properties
> import BoundedNat.BoundedNat
> import BoundedNat.Operations
> import BoundedNat.Properties
> import Sigma.Sigma
> import Sigma.Operations
> -- import Sigma.Properties
> import Nat.OperationsProperties
> import Nat.LTEProperties
> import Nat.LTProperties
> import Unit.Properties
> import Void.Properties
> import LocalEffect.Exception
> import LocalEffect.StdIO

> -- %default total
> %auto_implicits off

> -- %logging 5

Like "Example2.lidr", but now |step t x y| is empty in states
corresponding to |maxColumn|, no matter which |y| is selected! Thus,
such states are not viable for more than zero steps. Attemps at making
more than zero decision steps starting from |maxColumn| should be
detected and rejected.

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

** |Val| and |LTE|:

> SequentialDecisionProblems.CoreTheory.Val = 
>   Nat

> SequentialDecisionProblems.CoreTheory.plus = 
>   Prelude.Nat.plus

> SequentialDecisionProblems.CoreTheory.zero = 
>   Z

> SequentialDecisionProblems.CoreTheory.LTE = 
>   Prelude.Nat.LTE

> SequentialDecisionProblems.FullTheory.reflexiveLTE = 
>   Nat.LTEProperties.reflexiveLTE

> SequentialDecisionProblems.FullTheory.transitiveLTE = 
>   Nat.LTEProperties.transitiveLTE

> SequentialDecisionProblems.FullTheory.monotonePlusLTE = 
>   Nat.LTEProperties.monotoneNatPlusLTE

> SequentialDecisionProblems.OptDefaults.totalPreorderLTE = 
>   Nat.LTEProperties.totalPreorderLTE 

** Reward function:

> SequentialDecisionProblems.CoreTheory.reward t x y (MkSigma c _) =
>   if c == Z
>   then (S Z)
>   else if (S c) == nColumns
>        then (S (S Z))
>        else Z

** Measure:

> SequentialDecisionProblems.CoreTheory.meas = sum
> SequentialDecisionProblems.FullTheory.measMon = sumMon

** Reachability:

> SequentialDecisionProblems.CoreTheory.Reachable x' = Unit
> SequentialDecisionProblems.CoreTheory.reachableSpec1 {t} x r y = all (nexts t x y) where
>   all : (xs : List (State (S t))) -> SequentialDecisionProblems.CoreTheory.All (Reachable {t' = S t}) xs
>   all Nil = Nil
>   all (x :: xs) = () :: (all xs)

** |Ctrl| is finite:

> SequentialDecisionProblems.Utils.finiteCtrl _ = 
>   finiteLeftAheadRight

** Viability:

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

> SequentialDecisionProblems.CoreTheory.viableSpec1 {t} {n} x v with (decLT (outl x) maxColumn)
>   | (Yes prf) = MkSigma Ahead (ne, av) where
>     ne : NotEmpty (nexts t x Ahead)
>     ne = nextsLemma1 x prf
>     av : SequentialDecisionProblems.CoreTheory.All (Viable {t = S t} n) (nexts t x Ahead)
>     av = viableLemma x 
>   | (No _) = void v

> SequentialDecisionProblems.Utils.finiteViable {t} {n = Z}   _ = finiteUnit
> SequentialDecisionProblems.Utils.finiteViable {t} {n = S m} x with (decLT (outl x) maxColumn)
>   | (Yes p) = finiteUnit
>   | (No  c) = finiteVoid

> SequentialDecisionProblems.Utils.decidableViable {t} {n = Z}   _ = decidableUnit
> SequentialDecisionProblems.Utils.decidableViable {t} {n = S m} x with (decLT (outl x) maxColumn)
>   | (Yes _) = decidableUnit
>   | (No  _) = decidableVoid


* The computation:

> SequentialDecisionProblems.Utils.showState = show
> SequentialDecisionProblems.Utils.showCtrl = show

> computation : { [STDIO] } Eff ()
> computation =
>   do putStr ("enter number of steps:\n")
>      nSteps <- getNat
>      putStr ("enter initial column:\n")
>      x0 <- getLTB nColumns
>      case (decidableViable {t = Z} {n = nSteps} x0) of
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
