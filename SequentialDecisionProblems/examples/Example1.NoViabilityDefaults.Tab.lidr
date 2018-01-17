> module SequentialDecisionProblems.examples.Main

> import Decidable.Order

> import Control.Monad.Identity
> import Effects
> import Effect.Exception
> import Effect.StdIO

> import SequentialDecisionProblems.CoreTheory
> import SequentialDecisionProblems.FullTheory
> import SequentialDecisionProblems.TabBackwardsInduction
> import SequentialDecisionProblems.Utils
> import SequentialDecisionProblems.DeterministicDefaults
> import SequentialDecisionProblems.CoreTheoryOptDefaults
> import SequentialDecisionProblems.FullTheoryOptDefaults
> import SequentialDecisionProblems.TabBackwardsInductionOptDefaults

> import SequentialDecisionProblems.examples.LeftAheadRight

> import Identity.Operations
> import Identity.Properties
> import BoundedNat.BoundedNat
> import BoundedNat.Operations
> import BoundedNat.Properties
> import Sigma.Sigma
> import Nat.LTEProperties
> import Nat.LTProperties
> import Unit.Properties
> import LocalEffect.Exception
> import LocalEffect.StdIO

> -- %default total
> %auto_implicits off


The possibly simplest "cylinder" problem. |M| is the identity monad, the
state space is constant and we can move to the left, ahead or to the
right as we wish.

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
>   Id (MkSigma maxColumn (ltIdS maxColumn))
> SequentialDecisionProblems.CoreTheory.nexts t (MkSigma (S n) prf) Left =
>   Id (MkSigma n (ltLemma1 n nColumns prf))
> SequentialDecisionProblems.CoreTheory.nexts t (MkSigma n prf) Ahead =
>   Id (MkSigma n prf)
> SequentialDecisionProblems.CoreTheory.nexts t (MkSigma n prf) Right with (decLT n maxColumn)
>   | (Yes p)     = Id (MkSigma (S n) (LTESucc p))
>   | (No contra) = Id (MkSigma  Z    (LTESucc LTEZero))

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

> SequentialDecisionProblems.CoreTheory.meas (Id x) = x
> SequentialDecisionProblems.FullTheory.measMon f g prf (Id x) = prf x

** |State| is finite:

> SequentialDecisionProblems.TabBackwardsInduction.finiteState t = 
>   finiteLTB nColumns

** |Ctrl| is finite:

> SequentialDecisionProblems.Utils.finiteCtrl _ = 
>   finiteLeftAheadRight

** Reachability:

> SequentialDecisionProblems.CoreTheory.Reachable x' = Unit
> SequentialDecisionProblems.CoreTheory.reachableSpec1 x r y = ()
> SequentialDecisionProblems.TabBackwardsInduction.decidableReachable x = decidableUnit

** Viability

> SequentialDecisionProblems.CoreTheory.Viable n x =  Unit
> SequentialDecisionProblems.CoreTheory.viableSpec1 {t} x v = MkSigma Left (nonEmptyLemma (nexts t x Left), ())
> SequentialDecisionProblems.Utils.finiteViable n x = finiteUnit
> SequentialDecisionProblems.Utils.decidableViable n x = Yes ()


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
>                       -- ps   <- pure (backwardsInduction Z nSteps)
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
