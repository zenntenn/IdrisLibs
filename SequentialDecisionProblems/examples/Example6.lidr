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
> import SequentialDecisionProblems.NonDeterministicDefaults
> -- import SequentialDecisionProblems.ReachabilityDefaults
> import SequentialDecisionProblems.ViabilityDefaults
> import SequentialDecisionProblems.OptDefaults

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
> import Decidable.Properties
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

Like "Example2.lidr", but now the left and right boundaries are not
permeable and we have a barrier: at |t = 2|, |step t x y| is empty in
all states except for the one corresponding to |maxColumn|, no matter
which |y| is selected!  Thus, such states are not viable for more than
zero steps. Attemps at making more than 2 decision steps starting from
states from which the state corresponding to |maxColumn| at |t = 2|
cannot be reached should be detected and rejected.

* The decision process:

> maxColumn : Nat
> maxColumn = 4

> nColumns : Nat
> nColumns = S maxColumn

** States:

> SequentialDecisionProblems.CoreTheory.State t = LTB nColumns

** Controls:

> SequentialDecisionProblems.CoreTheory.Ctrl t x = LeftAheadRight

** Transition function:

> SequentialDecisionProblems.CoreTheory.nexts Z (MkSigma  Z    prf) Left = 
>   []
> SequentialDecisionProblems.CoreTheory.nexts Z (MkSigma (S n) prf) Left =
>   [MkSigma n (ltLemma1 n nColumns prf)]
> SequentialDecisionProblems.CoreTheory.nexts Z x Ahead = 
>   [x]
> SequentialDecisionProblems.CoreTheory.nexts Z (MkSigma n prf) Right with (decLT n maxColumn)
>   | (Yes p)     = [MkSigma (S n) (LTESucc p)]
>   | (No contra) = []

> SequentialDecisionProblems.CoreTheory.nexts (S Z) (MkSigma  Z    prf) Left = 
>   []
> SequentialDecisionProblems.CoreTheory.nexts (S Z) (MkSigma (S n) prf) Left =
>   [MkSigma n (ltLemma1 n nColumns prf)]
> SequentialDecisionProblems.CoreTheory.nexts (S Z) x Ahead = 
>   [x]
> SequentialDecisionProblems.CoreTheory.nexts (S Z) (MkSigma n prf) Right with (decLT n maxColumn)
>   | (Yes p)     = [MkSigma (S n) (LTESucc p)]
>   | (No contra) = []

> SequentialDecisionProblems.CoreTheory.nexts (S (S Z)) _ Left =
>   []
> SequentialDecisionProblems.CoreTheory.nexts (S (S Z)) (MkSigma n prf) Ahead with (decEq n maxColumn)
>   | (Yes p)     = [MkSigma n prf]
>   | (No contra) = []
> SequentialDecisionProblems.CoreTheory.nexts (S (S Z)) _ Right =
>   []

> SequentialDecisionProblems.CoreTheory.nexts (S (S (S t))) (MkSigma  Z    prf) Left = 
>   []
> SequentialDecisionProblems.CoreTheory.nexts (S (S (S t))) (MkSigma (S n) prf) Left =
>   [MkSigma n (ltLemma1 n nColumns prf)]
> SequentialDecisionProblems.CoreTheory.nexts (S (S (S t))) x Ahead = 
>   [x]
> SequentialDecisionProblems.CoreTheory.nexts (S (S (S t))) (MkSigma n prf) Right with (decLT n maxColumn)
>   | (Yes p)     = [MkSigma (S n) (LTESucc p)]
>   | (No contra) = []

** Reward function:

> SequentialDecisionProblems.CoreTheory.Val = Nat

> SequentialDecisionProblems.CoreTheory.reward t x y (MkSigma c _) =
>   if c == Z then S Z else Z

> SequentialDecisionProblems.CoreTheory.plus = Prelude.Nat.plus
> SequentialDecisionProblems.CoreTheory.zero = Z

> SequentialDecisionProblems.CoreTheory.LTE = Prelude.Nat.LTE
> SequentialDecisionProblems.FullTheory.reflexiveLTE = Nat.LTEProperties.reflexiveLTE
> SequentialDecisionProblems.FullTheory.transitiveLTE = Nat.LTEProperties.transitiveLTE
> SequentialDecisionProblems.FullTheory.monotonePlusLTE = Nat.LTEProperties.monotoneNatPlusLTE

** M is measurable:

> SequentialDecisionProblems.CoreTheory.meas = sum
> SequentialDecisionProblems.FullTheory.measMon = sumMon

* Reachable

> -- Reachable : State t' -> Type
> SequentialDecisionProblems.CoreTheory.Reachable x' = Unit

> -- reachableSpec1 : (x : State t) -> Reachable {t' = t} x -> (y : Ctrl t x) -> All (Reachable {t' = S t}) (nexts t x y)
> SequentialDecisionProblems.CoreTheory.reachableSpec1 {t} x r y = all (nexts t x y) where
>   all : (xs : List (State (S t))) -> SequentialDecisionProblems.CoreTheory.All (Reachable {t' = S t}) xs
>   all Nil = Nil
>   all (x :: xs) = MkUnit :: (all xs)


* |cvalargmax| and |cvalmax| 

> -- totalPreorderLTE : TotalPreorder SequentialDecisionProblems.CoreTheory.LTE
> SequentialDecisionProblems.OptDefaults.totalPreorderLTE = 
>   MkTotalPreorder Prelude.Nat.LTE
>                   Nat.LTEProperties.reflexiveLTE 
>                   Nat.LTEProperties.transitiveLTE 
>                   Nat.LTEProperties.totalLTE

> -- finiteCtrl : {t : Nat} -> {n : Nat} -> (x : State t) -> Finite (Ctrl t x) 
> SequentialDecisionProblems.Utils.finiteCtrl _ = finiteLeftAheadRight
> %freeze SequentialDecisionProblems.Utils.finiteCtrl

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
