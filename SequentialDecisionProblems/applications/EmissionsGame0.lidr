> module SequentialDecisionProblems.applications.Main

> import Data.Fin
> import Data.List
> import Data.List.Quantifiers
> import Data.So
> import Control.Isomorphism
> import Effects
> import Effect.Exception
> import Effect.StdIO

> import SequentialDecisionProblems.CoreTheory
> import SequentialDecisionProblems.FullTheory
> import SequentialDecisionProblems.Utils
> import SequentialDecisionProblems.FastStochasticDefaults
> import SequentialDecisionProblems.CoreTheoryOptDefaults
> import SequentialDecisionProblems.FullTheoryOptDefaults

> import SequentialDecisionProblems.applications.FreezeOrIncrease
> import SequentialDecisionProblems.applications.GoodOrBad

> import FastSimpleProb.SimpleProb
> import FastSimpleProb.BasicOperations
> import FastSimpleProb.BasicProperties
> import FastSimpleProb.MonadicOperations
> import FastSimpleProb.MonadicProperties
> import FastSimpleProb.Measures
> import FastSimpleProb.MeasuresProperties
> import Sigma.Sigma
> import Sigma.Operations
> import Sigma.Properties
> import Nat.LTProperties
> import Double.Predicates
> import NonNegDouble.NonNegDouble
> import NonNegDouble.Constants
> import NonNegDouble.BasicOperations
> import NonNegDouble.Operations
> import NonNegDouble.Properties
> import NonNegDouble.Predicates
> import NonNegDouble.LTEProperties
> import NonNegDouble.Measures
> import NonNegDouble.MeasureProperties
> import Finite.Predicates
> import Finite.Operations
> import Finite.Properties
> import Unique.Predicates
> import Decidable.Predicates
> import LocalEffect.Exception
> import LocalEffect.StdIO
> import Fin.Operations
> import Fraction.Fraction
> import Fraction.Normal
> import Nat.Positive
> import List.Operations
> import Unit.Properties

> -- %default total
> %auto_implicits off

> -- %logging 5


* Introduction

We specify a first emissions game as a stochastic sequential decision
problem.


* Controls

At each decision step, the decision maker has two options: freezing
emissions or increasing emissions:

> SequentialDecisionProblems.CoreTheory.Ctrl _ _ = FreezeOrIncrease


* States

The decision maker can observe three values: the cumulated effects of
its own decisions, of the decisions taken by "others", and a state of
the world. The latter can be either good or bad

> SequentialDecisionProblems.CoreTheory.State t = (Nat, Nat, GoodOrBad)

The idea is that the world starts in a good state but, if the sum of the
cumulated emissions of the decision maker and of the "others" increase
beyond a certain threshold, there is a non-zero probability to turn to a
bad state. Once there, there is no chance to come back to a good state.

In this game, we assume that the decision maker and the "others" take
the same decisions in a competitive setup, see section on rewards.


* Transition function

> threshold : Nat
> threshold = Z

> p   :  Double
> p   =  1.0

> p1  :  NonNegDouble
> p1  =  cast (p   / (p + 1.0))
> p2  :  NonNegDouble
> p2  =  cast (1.0 / (p + 1.0))

> SequentialDecisionProblems.CoreTheory.nexts t (s1, s2, Good) Freeze =
>   if (s1 + s2 <= threshold)
>   then mkSimpleProb [((s1, s2, Good), one)]
>   else mkSimpleProb [((s1, s2, Good), p1), ((s1, s2, Bad), p2)]

> SequentialDecisionProblems.CoreTheory.nexts t (s1, s2, Good) Increase = 
>   if (s1 + s2 <= threshold)
>   then mkSimpleProb [((S s1, S s2, Good), one)]
>   else mkSimpleProb [((S s1, S s2, Good), p1), ((S s1, S s2, Bad), p2)]

> SequentialDecisionProblems.CoreTheory.nexts t (s1, s2, Bad) Freeze = 
>   mkSimpleProb [((s1, s2, Bad), one)]

> SequentialDecisionProblems.CoreTheory.nexts t (s1, s2, Bad) Increase = 
>   mkSimpleProb [((S s1, S s2, Bad), one)]


* |Val| and |LTE|:

> SequentialDecisionProblems.CoreTheory.Val = 
>   NonNegDouble.NonNegDouble

> SequentialDecisionProblems.CoreTheory.plus = 
>   NonNegDouble.Operations.plus

> SequentialDecisionProblems.CoreTheory.zero = 
>   fromInteger @{NumNonNegDouble} 0

> SequentialDecisionProblems.CoreTheory.LTE = 
>   NonNegDouble.Predicates.LTE

> SequentialDecisionProblems.FullTheory.reflexiveLTE = 
>   NonNegDouble.LTEProperties.reflexiveLTE

> SequentialDecisionProblems.FullTheory.transitiveLTE = 
>   NonNegDouble.LTEProperties.transitiveLTE

> SequentialDecisionProblems.FullTheory.monotonePlusLTE = 
>   NonNegDouble.LTEProperties.monotonePlusLTE

> SequentialDecisionProblems.CoreTheoryOptDefaults.totalPreorderLTE = 
>   NonNegDouble.LTEProperties.totalPreorderLTE 


* Reward function

The idea is that, at every step, being in a good world yields more
benefits than being in a bad world:

> benefitsGood : NonNegDouble
> benefitsGood = one

> benefitsBad  : NonNegDouble
> benefitsBad  = NonNegDouble.Constants.zero

Freezing emissions also brings less benefits than increasing
emissions. However, increasing emissions in a bad world yields less
benefits than increasing emissions in a good world:

> benefitsFreeze : NonNegDouble
> benefitsFreeze = NonNegDouble.Constants.zero

> benefitsIncreaseGood : NonNegDouble
> benefitsIncreaseGood = one

> benefitsIncreaseBad : NonNegDouble
> benefitsIncreaseBad = cast 0.9


> using implementation NumNonNegDouble
> 
>   SequentialDecisionProblems.CoreTheory.reward _ (_, _, _) Freeze   (_, _, Good) = benefitsGood + benefitsFreeze
>   SequentialDecisionProblems.CoreTheory.reward _ (_, _, _) Increase (_, _, Good) = benefitsGood + benefitsIncreaseGood
>   SequentialDecisionProblems.CoreTheory.reward _ (_, _, _) Freeze   (_, _,  Bad) = benefitsBad  + benefitsFreeze
>   SequentialDecisionProblems.CoreTheory.reward _ (_, _, _) Increase (_, _,  Bad) = benefitsBad  + benefitsIncreaseBad


* Completing the problem specification

To be able to apply the verified, generic backwards induction algorithm
of |CoreTheory| to compute optimal policies for our problem, we have to
explain how the decision maker accounts for uncertainties on rewards
induced by uncertainties in the transition function. We first assume
that the decision maker measures uncertain rewards by their expected
value:

> SequentialDecisionProblems.CoreTheory.meas = expectedValue
> SequentialDecisionProblems.FullTheory.measMon = monotoneExpectedValue

Further on, we have to implement the notions of viability and
reachability. We start by positing that all states are viable for any
number of steps:

> -- Viable : (n : Nat) -> State t -> Type
> SequentialDecisionProblems.CoreTheory.Viable n x = Unit

From this definition, it trivially follows that all elements of an
arbitrary list of states are viable for an arbitrary number of steps:

> viableLemma : {t, n : Nat} -> (xs : List (State t)) -> All (Viable n) xs
> viableLemma  Nil      = Nil
> viableLemma {t} {n} (x :: xs) = () :: (viableLemma {t} {n} xs)

This fact and the (less trivial) result that simple probability
distributions are never empty, see |nonEmptyLemma| in
|MonadicProperties| in |SimpleProb|, allows us to show that the above
definition of |Viable| fulfills |viableSpec1|:

> -- viableSpec1 : (x : State t) -> Viable (S n) x -> GoodCtrl t x 
> SequentialDecisionProblems.CoreTheory.viableSpec1 {t} {n} s v = 
>   MkSigma Freeze (ne, av) where
>     ne : SequentialDecisionProblems.CoreTheory.NotEmpty (nexts t s Freeze)
>     ne = nonEmptyLemma (nexts t s Freeze)
>     av : SequentialDecisionProblems.CoreTheory.All (Viable {t = S t} n) (nexts t s Freeze)
>     av = viableLemma {t = S t} (support (nexts t s Freeze))

> SequentialDecisionProblems.Utils.finiteViable n x = finiteUnit

> SequentialDecisionProblems.Utils.decidableViable n x = decidableUnit

For reachability, we proceed in a similar way. We say that all states
are reachable

> -- Reachable : State t' -> Type
> SequentialDecisionProblems.CoreTheory.Reachable x' = Unit

which immediately implies |reachableSpec1|:

> -- reachableSpec1 : (x : State t) -> Reachable {t' = t} x -> (y : Ctrl t x) -> All (Reachable {t' = S t}) (nexts t x y)
> SequentialDecisionProblems.CoreTheory.reachableSpec1 {t} x r y = all (nexts t x y) where
>   all : (sp : SimpleProb  (State (S t))) -> SequentialDecisionProblems.CoreTheory.All (Reachable {t' = S t}) sp
>   all sp = all' (support sp) where
>     all' : (xs : List (State (S t))) -> Data.List.Quantifiers.All (Reachable {t' = S t}) xs
>     all' Nil = Nil
>     all' (x :: xs) = () :: (all' xs)

Finally, we have to show that controls are finite

> -- finiteCtrl : {t : Nat} -> (x : State t) -> Finite (Ctrl t x) 
> SequentialDecisionProblems.Utils.finiteCtrl _ = finiteFreezeOrIncrease


* Optimal policies, optimal decisions, ...

We can now apply the results of our |CoreTheory| and of the |FullTheory|
to compute verified optimal policies, possible state-control sequences,
etc. To this end, we need to be able to show the outcome of the decision
process. This means implemeting functions to print states and controls:

> -- showState : {t : Nat} -> State t -> String
> SequentialDecisionProblems.Utils.showState {t} (s1, s2, Good) = 
>   "(" ++ show s1 ++ "," ++ show s2 ++ ",Good)" 
> SequentialDecisionProblems.Utils.showState {t} (s1, s2, Bad) = 
>   "(" ++ show s1 ++ "," ++ show s2 ++ ",Bad)" 

> -- showControl : {t : Nat} -> {x : State t} -> Ctrl t x -> String
> SequentialDecisionProblems.Utils.showCtrl {t} {x} Freeze = "Freeze"
> SequentialDecisionProblems.Utils.showCtrl {t} {x} Increase = "Increase"


> computation : { [STDIO] } Eff ()
> computation =
>   do putStr ("enter number of steps:\n")
>      nSteps <- getNat
>      case (decidableViable {t = Z} nSteps (Z, Z, Good)) of
>        (Yes v) => do putStrLn ("computing optimal policies ...")
>                      ps   <- pure (backwardsInduction Z nSteps)
>                      putStrLn ("computing optimal controls ...")
>                      mxys <- pure (possibleStateCtrlSeqs (Z, Z, Good) () v ps)
>                      putStrLn "possible state-control sequences:"
>                      putStr "  "
>                      putStrLn (show mxys)
>                      -- mvs <- pure (possibleRewards' mxys)
>                      -- putStrLn "possible rewards:"
>                      -- putStr "  "
>                      -- putStrLn (show mvs)
>                      -- mxyvs <- pure (possibleStateCtrlSeqsRewards' mxys)
>                      -- putStrLn "possible state-control sequences and rewards:"
>                      -- putStr "  "
>                      -- putStrLn (show mxyvs)
>                      -- putStrLn "measure of possible rewards: "
>                      -- putStr "  "
>                      -- putStrLn (show (meas mvs))
>                      -- argmaxmax <- pure (argmaxMax {A = StateCtrlSeq Z nSteps} {B = Val} totalPreorderLTE (support mxyvs) (nonEmptyLemma mxyvs))
>                      -- putStrLn "best possible state-control sequence: "
>                      -- putStr "  "
>                      -- putStrLn (show (fst argmaxmax))
>                      -- putStrLn "best possible reward: "
>                      -- putStr "  "
>                      -- putStrLn (show (snd argmaxmax))
>                      -- -- argminmin <- pure (argminMin totalPreorderLTE (support mxyvs) (nonEmptyLemma mxyvs))
>                      -- -- putStrLn "worst possible state-control sequence: "
>                      -- -- putStr "  "
>                      -- -- putStrLn (show (fst argminmin))
>                      -- -- putStrLn "worst possible reward: "
>                      -- -- putStr "  "
>                      -- -- putStrLn (show (snd argminmin))
>                      putStrLn ("done!")                       
>        (No _)  => putStrLn ("initial state non viable for " ++ cast {from = Int} (cast nSteps) ++ " steps")

> main : IO ()
> main = run computation


> {-

> ---}


[1] Stanford Encyclopedia of Phylosophy, Causal Decision Theory, 2010


-- Local Variables:
-- idris-packages: ("effects")
-- End:
 
 
