> module SequentialDecisionProblems.examples.Main

> import Data.List
> import Data.List.Quantifiers
> import Effects
> import Effect.Exception
> import Effect.StdIO

> import SequentialDecisionProblems.CoreTheory
> import SequentialDecisionProblems.FullTheory
> import SequentialDecisionProblems.TabBackwardsInduction
> import SequentialDecisionProblems.Utils
> import SequentialDecisionProblems.StochasticDefaults
> import SequentialDecisionProblems.CoreTheoryOptDefaults
> import SequentialDecisionProblems.FullTheoryOptDefaults
> import SequentialDecisionProblems.TabBackwardsInductionOptDefaults

> import SequentialDecisionProblems.examples.LeftAheadRight

> import SimpleProb.SimpleProb
> import SimpleProb.BasicOperations
> import SimpleProb.BasicProperties
> import SimpleProb.MonadicOperations
> import SimpleProb.MonadicProperties
> import SimpleProb.Measures
> import SimpleProb.MeasuresProperties
> import BoundedNat.BoundedNat
> import BoundedNat.Operations
> import BoundedNat.Properties
> import Sigma.Sigma
> import Nat.LTProperties
> import NonNegRational.NonNegRational
> import NonNegRational.BasicOperations
> import NonNegRational.BasicProperties
> import NonNegRational.Predicates
> import NonNegRational.LTEProperties
> import Void.Properties
> import Unit.Properties
> import LocalEffect.Exception
> import LocalEffect.StdIO

> -- %default total
> %auto_implicits off

> -- %logging 5

We reimplement "Example2.lidr", this time with |M = SimpleProb|.

* The decision process:

> maxColumn : Nat
> maxColumn = 10
> %freeze maxColumn

> nColumns : Nat
> nColumns = S maxColumn

** States:

> SequentialDecisionProblems.CoreTheory.State t = LTB nColumns

** Controls:

> SequentialDecisionProblems.CoreTheory.Ctrl t x = LeftAheadRight

** Transition function:

> SequentialDecisionProblems.CoreTheory.nexts t (MkSigma Z prf) Left =
>   SimpleProb.MonadicOperations.ret (MkSigma maxColumn (ltIdS maxColumn))
> SequentialDecisionProblems.CoreTheory.nexts t (MkSigma (S n) prf) Left =
>   SimpleProb.MonadicOperations.ret (MkSigma n (ltLemma1 n nColumns prf))
> SequentialDecisionProblems.CoreTheory.nexts t x Ahead = SimpleProb.MonadicOperations.ret x
> SequentialDecisionProblems.CoreTheory.nexts t (MkSigma n prf) Right with (decLT n maxColumn)
>   | (Yes p)     = SimpleProb.MonadicOperations.ret (MkSigma (S n) (LTESucc p))
>   | (No contra) = SimpleProb.MonadicOperations.ret (MkSigma  Z    (LTESucc LTEZero))

** |Val| and |LTE|:

> SequentialDecisionProblems.CoreTheory.Val = 
>   NonNegRational.NonNegRational

> SequentialDecisionProblems.CoreTheory.plus = 
>   NonNegRational.BasicOperations.plus

> SequentialDecisionProblems.CoreTheory.zero = 
>   fromInteger 0

> SequentialDecisionProblems.CoreTheory.LTE = 
>   NonNegRational.Predicates.LTE

> SequentialDecisionProblems.FullTheory.reflexiveLTE = 
>   NonNegRational.LTEProperties.reflexiveLTE

> SequentialDecisionProblems.FullTheory.transitiveLTE = 
>   NonNegRational.LTEProperties.transitiveLTE

> SequentialDecisionProblems.FullTheory.monotonePlusLTE = 
>   NonNegRational.LTEProperties.monotonePlusLTE

> SequentialDecisionProblems.CoreTheoryOptDefaults.totalPreorderLTE = 
>   NonNegRational.LTEProperties.totalPreorderLTE 

** Reward function:

> SequentialDecisionProblems.CoreTheory.reward t x y (MkSigma c _) =
>   if c == Z
>   then (fromInteger 1)
>   else if (S c) == nColumns
>        then (fromInteger 2)
>        else (fromInteger 0)

** Measure:

> SequentialDecisionProblems.CoreTheory.meas = expectedValue
> SequentialDecisionProblems.FullTheory.measMon = monotoneExpectedValue

** |State| is finite:

> SequentialDecisionProblems.TabBackwardsInduction.finiteState t = 
>   finiteLTB nColumns

** |Ctrl| is finite:

> SequentialDecisionProblems.Utils.finiteCtrl _ = 
>   finiteLeftAheadRight

** Reachability

> SequentialDecisionProblems.CoreTheory.Reachable x' = Unit
> SequentialDecisionProblems.CoreTheory.reachableSpec1 {t} x r y = all (nexts t x y) where
>   all : (sp : SimpleProb  (State (S t))) -> SequentialDecisionProblems.CoreTheory.All (Reachable {t' = S t}) sp
>   all sp = all' (support sp) where
>     all' : (xs : List (State (S t))) -> Data.List.Quantifiers.All (Reachable {t' = S t}) xs
>     all' Nil = Nil
>     all' (x :: xs) = () :: (all' xs)
> SequentialDecisionProblems.TabBackwardsInduction.decidableReachable x = decidableUnit

** Viability:

> SequentialDecisionProblems.CoreTheory.Viable n x = Unit

> SequentialDecisionProblems.CoreTheory.viableSpec1 {t} {n} x _ = MkSigma Ahead (ne, av) where
>   ne : SequentialDecisionProblems.CoreTheory.NotEmpty (nexts t x Ahead)
>   ne = nonEmptyLemma (nexts t x Ahead) 
>   av : SequentialDecisionProblems.CoreTheory.All (Viable {t = S t} n) (nexts t x Ahead)
>   av = [()]

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
