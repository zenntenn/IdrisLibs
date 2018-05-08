> module SequentialDecisionProblems.examples.Main

> -- import Decidable.Order

> import Data.List
> import Data.List.Quantifiers
> import Effects
> import Effect.Exception
> import Effect.StdIO

> import SequentialDecisionProblems.CoreTheory
> import SequentialDecisionProblems.FullTheory
> import SequentialDecisionProblems.Utils
> import SequentialDecisionProblems.StochasticDefaults
> import SequentialDecisionProblems.CoreTheoryOptDefaults
> import SequentialDecisionProblems.FullTheoryOptDefaults
> import SequentialDecisionProblems.ViabilityDefaults

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
> import LocalEffect.Exception
> import LocalEffect.StdIO
> import Fraction.Fraction
> import Fraction.Normal
> import Nat.Positive
> import List.Operations

> -- %default total
> %auto_implicits off

> -- %logging 5

Like "Example4.lidr", but selecting "Left" yields a non-zero
probablility to move "Ahead"!

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

> oo2  : NonNegRational
> oo2  = fromFraction (1, Element 2 MkPositive)

> SequentialDecisionProblems.CoreTheory.nexts t (MkSigma Z prf) Left =
>   SimpleProb.MonadicOperations.ret (MkSigma maxColumn (ltIdS maxColumn))
> SequentialDecisionProblems.CoreTheory.nexts t (MkSigma (S n) prf) Left =
>   MkSimpleProb [(MkSigma (S n) prf, oo2), 
>                 (MkSigma n (ltLemma1 n nColumns prf), oo2)] Refl

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


* The computation:

> SequentialDecisionProblems.Utils.showState = show @{ShowLTB}
> SequentialDecisionProblems.Utils.showCtrl = show

> %freeze possibleStateCtrlSeqs
> %freeze possibleRewards'
> %freeze possibleStateCtrlSeqsRewards'
> %freeze meas
> %freeze support
> %freeze nonEmptyLemma
> %freeze totalPreorderLTE
> %freeze argmaxMax
> %freeze argminMin

> computation : { [STDIO] } Eff ()
> computation =
>   do putStr ("enter number of steps:\n")
>      nSteps <- getNat
>      putStr ("enter initial column:\n")
>      x0 <- getLTB nColumns
>      case (decidableViable {t = Z} nSteps x0) of
>        (Yes v0) => do putStrLn ("computing optimal policies ...")
>                       ps   <- pure (backwardsInduction Z nSteps)
>                       putStrLn ("computing optimal controls ...")
>                       mxys <- pure (possibleStateCtrlSeqs x0 () v0 ps)
>                       putStrLn "possible state-control sequences:"
>                       putStr "  "
>                       putStrLn (show mxys)
>                       mvs <- pure (possibleRewards' mxys)
>                       putStrLn "possible rewards:"
>                       putStr "  "
>                       putStrLn (show mvs)
>                       -- mxyvs <- pure (possibleStateCtrlSeqsRewards' mxys)
>                       -- putStrLn "possible state-control sequences and rewards:"
>                       -- putStr "  "
>                       -- putStrLn (show mxyvs)
>                       -- putStrLn "measure of possible rewards: "
>                       -- putStr "  "
>                       -- putStrLn (show (meas mvs))
>                       -- argmaxmax <- pure (argmaxMax {A = StateCtrlSeq Z nSteps} {B = Val} totalPreorderLTE (support mxyvs) (nonEmptyLemma mxyvs))
>                       -- putStrLn "best possible state-control sequence: "
>                       -- putStr "  "
>                       -- putStrLn (show (fst argmaxmax))
>                       -- putStrLn "best possible reward: "
>                       -- putStr "  "
>                       -- putStrLn (show (snd argmaxmax))
>                       -- -- argminmin <- pure (argminMin totalPreorderLTE (support mxyvs) (nonEmptyLemma mxyvs))
>                       -- -- putStrLn "worst possible state-control sequence: "
>                       -- -- putStr "  "
>                       -- -- putStrLn (show (fst argminmin))
>                       -- -- putStrLn "worst possible reward: "
>                       -- -- putStr "  "
>                       -- -- putStrLn (show (snd argminmin))
>                       putStrLn ("done!")                       
>        (No _)   => putStrLn ("initial column non viable for " ++ cast {from = Int} (cast nSteps) ++ " steps")

> main : IO ()
> main = run computation


> {-

> ---}


-- Local Variables:
-- idris-packages: ("effects")
-- End:
