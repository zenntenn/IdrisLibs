> module SequentialDecisionProblems.examples.Main

> import Decidable.Order

> import Data.List
> import Data.List.Quantifiers
> import Effects
> import Effect.Exception
> import Effect.StdIO

> import SequentialDecisionProblems.CoreTheory
> import SequentialDecisionProblems.FullTheory
> import SequentialDecisionProblems.TabBackwardsInduction
> import SequentialDecisionProblems.Utils
> import SequentialDecisionProblems.NonDeterministicDefaults
> import SequentialDecisionProblems.CoreTheoryOptDefaults
> import SequentialDecisionProblems.FullTheoryOptDefaults
> import SequentialDecisionProblems.TabBackwardsInductionOptDefaults

> import SequentialDecisionProblems.examples.LeftAheadRight

> import List.Operations
> import List.Properties
> import BoundedNat.BoundedNat
> import BoundedNat.Operations
> import BoundedNat.Properties
> import Sigma.Sigma
> import Nat.OperationsProperties
> import Nat.LTEProperties
> import Nat.LTProperties
> import Unit.Properties
> import LocalEffect.Exception
> import LocalEffect.StdIO

> -- %default total
> %auto_implicits off

> -- %logging 5


We reimplement "Example1.lidr", this time with |M = List|.

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
> SequentialDecisionProblems.CoreTheory.nexts t (MkSigma (S n) prf) Left =
>   [MkSigma n (ltLemma1 n nColumns prf)]
> SequentialDecisionProblems.CoreTheory.nexts t x Ahead = [x]
> SequentialDecisionProblems.CoreTheory.nexts t (MkSigma n prf) Right with (decLT n maxColumn)
>   | (Yes p)     = [MkSigma (S n) (LTESucc p)]
>   | (No contra) = [MkSigma  Z    (LTESucc LTEZero)]

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

> SequentialDecisionProblems.CoreTheoryOptDefaults.totalPreorderLTE = 
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

** |State| is finite:

> SequentialDecisionProblems.TabBackwardsInduction.finiteState t = 
>   finiteLTB nColumns

** |Ctrl| is finite:

> SequentialDecisionProblems.Utils.finiteCtrl _ = 
>   finiteLeftAheadRight

** Reachability:

> SequentialDecisionProblems.CoreTheory.Reachable x' = Unit
> SequentialDecisionProblems.CoreTheory.reachableSpec1 {t} x r y = all (nexts t x y) where
>   all : (xs : List (State (S t))) -> SequentialDecisionProblems.CoreTheory.All (Reachable {t' = S t}) xs
>   all Nil = Nil
>   all (x :: xs) = () :: (all xs)
> SequentialDecisionProblems.TabBackwardsInduction.decidableReachable x = decidableUnit

** Viability:

> SequentialDecisionProblems.CoreTheory.Viable n x =  Unit

> nextsNotEmptyLemma : {t : Nat} -> 
>                      (x : State t) -> 
>                      SequentialDecisionProblems.CoreTheory.NotEmpty (nexts t x Ahead)
> nextsNotEmptyLemma {t} x = 
>   SequentialDecisionProblems.CoreTheory.elemNotEmptySpec0 {A = State (S t)} x [x] Here

> viableLemma : {t : Nat} -> {n : Nat} ->
>               (x : State t) -> 
>               SequentialDecisionProblems.CoreTheory.All (Viable {t = S t} n) (nexts t x Ahead)
> viableLemma (MkSigma n prf) = [()]

> SequentialDecisionProblems.CoreTheory.viableSpec1 {t} {n} x _ = MkSigma Ahead (ne, av) where
>   ne : NotEmpty (nexts t x Ahead)
>   ne = nextsNotEmptyLemma {t} x
>   av : SequentialDecisionProblems.CoreTheory.All (Viable {t = S t} n) (nexts t x Ahead)
>   av = viableLemma x
> SequentialDecisionProblems.Utils.finiteViable n x = finiteUnit
> SequentialDecisionProblems.Utils.decidableViable n x = decidableUnit


* The computation:

> SequentialDecisionProblems.Utils.showState = show @{ShowLTB}
> SequentialDecisionProblems.Utils.showCtrl = show

> computation : { [STDIO] } Eff ()
> computation =
>   do putStr ("enter number of steps:\n")
>      nSteps <- getNat
>      putStr ("enter initial column:\n")
>      x0 <- getLTB nColumns
>      case (decidableViable {t = Z} nSteps x0) of
>        (Yes v0) => do putStrLn ("computing optimal policies ...")
>                       ps   <- pure (tabTailRecursiveBackwardsInduction Z nSteps)
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
