> module SequentialDecisionProblems.applications.Main

> import Data.Fin
> import Data.List
> import Data.List.Quantifiers
> import Data.So
> import Effects
> import Effect.Exception
> import Effect.StdIO

> import SequentialDecisionProblems.CoreTheory
> import SequentialDecisionProblems.FullTheory
> import SequentialDecisionProblems.TabBackwardsInduction
> import SequentialDecisionProblems.Utils
> import SequentialDecisionProblems.FastStochasticDefaults
> import SequentialDecisionProblems.CoreTheoryOptDefaults
> import SequentialDecisionProblems.FullTheoryOptDefaults
> import SequentialDecisionProblems.TabBackwardsInductionOptDefaults

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
> import Double.Predicates
> import Double.Postulates
> import Double.Operations
> import Double.Properties
> import NonNegDouble.NonNegDouble
> import NonNegDouble.Constants
> import NonNegDouble.BasicOperations
> import NonNegDouble.Operations
> import NonNegDouble.Properties
> import NonNegDouble.Predicates
> import NonNegDouble.LTEProperties
> import Finite.Predicates
> import Finite.Operations
> import Finite.Properties
> import Decidable.Predicates
> import Decidable.Properties
> import LocalEffect.Exception
> import LocalEffect.StdIO
> import Fin.Operations
> import List.Operations
> import Unit.Properties

> -- %default total
> %auto_implicits off

> -- %logging 5


* Introduction

We specify a first emissions game as a stochastic sequential decision
problem with a single decision maker.


* Controls

At each decision step, the decision maker has two options: freezing
emissions or increasing emissions:

> SequentialDecisionProblems.CoreTheory.Ctrl _ _ = FreezeOrIncrease


* States

At each decision step, the decision maker has to choose an option on the
bases of two data: the amount of cumulated emissions and the state of
the world. The latter can be either good or bad:

> SequentialDecisionProblems.CoreTheory.State t = (Fin (S t), GoodOrBad)

The idea is that the game starts with zero cumulated emissions and with
the world in the good state. In these conditions, the probability to
turn to the bad state is low. But if the cumulated emissions increase
beyond a critical threshold, the probability that the state of the world
turns bad increases.  If the world is the bad state, there is no chance
to come back to the good state. As for controls, it is useful to show
that |State| is finite:


* Transition function

> -- The critical threshold
> cr : Double
> cr = 0.0

> -- The probability of staying in a good world when the cumulated
> -- emissions are below the critical threshold
> p1  :  NonNegDouble
> p1  =  cast 0.65

> -- The probabilities of staying in a good world when the cumulated
> -- emissions are above the critical threshold
> p2  :  NonNegDouble
> p2  =  cast 0.1

> -- The transition function: good world, freezing emissions
> SequentialDecisionProblems.CoreTheory.nexts t (e, Good) Freeze =
>   let goodState = (weaken e, Good) in
>   let badState  = (weaken e, Bad) in
>   if (fromFin e <= cr)
>   then mkSimpleProb [(goodState, p1), (badState, one - p1)]
>   else mkSimpleProb [(goodState, p2), (badState, one - p2)]

> -- The transition function: good world, increasing emissions
> SequentialDecisionProblems.CoreTheory.nexts t (e, Good) Increase =
>   let goodState = (FS e, Good) in
>   let badState  = (FS e, Bad) in
>   if (fromFin e <= cr)  then mkSimpleProb [(goodState, p1), (badState, one - p1)]
>                         else mkSimpleProb [(goodState, p2), (badState, one - p2)]

> -- The transition function: bad world, freezing emissions
> SequentialDecisionProblems.CoreTheory.nexts t (e, Bad) Freeze =
>   let badState  = (weaken e, Bad) in mkSimpleProb [(badState, one)]

> -- The transition function: bad world, increasing emissions
> SequentialDecisionProblems.CoreTheory.nexts t (e, Bad) Increase =
>   let badState  = (FS e, Bad) in mkSimpleProb [(badState, one)]

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

The idea is that being in a good world yields one unit of benefits per
step and being in a bad world yield less benefits:

> -- Ratio of the benefits in a bad world and the benefits in a good world
> badOverGood : NonNegDouble
> badOverGood = cast 0.5

> -- Sanity check
> badOverGoodLTEone : badOverGood `NonNegDouble.Predicates.LTE` one
> badOverGoodLTEone = MkLTE Oh

Emitting greenhouse gases also brings benefits. These are a fraction of
the step benefits in a good world and freezing emissions brings less
benefits than increasing emissions:

> -- Ratio between freezing emissions benefits and step benefits (in a good world)
> freezeOverGood : NonNegDouble
> freezeOverGood = cast 0.1

> -- Ratio between increasing emissions benefits and step benefits (in a good world)
> increaseOverGood : NonNegDouble
> increaseOverGood = cast 0.3

> -- Sanity check
> freezeOverGoodLTEone : freezeOverGood `NonNegDouble.Predicates.LTE` one
> freezeOverGoodLTEone = MkLTE Oh

> -- Sanity check
> increaseOverGoodLTEone : increaseOverGood `NonNegDouble.Predicates.LTE` one
> increaseOverGoodLTEone = MkLTE Oh

> -- Sanity check
> freezeLTEincrease : freezeOverGood `NonNegDouble.Predicates.LTE` increaseOverGood
> freezeLTEincrease = MkLTE Oh

> -- Reward function:
> 
> using implementation NumNonNegDouble
> 
>   SequentialDecisionProblems.CoreTheory.reward _ _ Freeze   (_, Good) =
>     one                       + one * freezeOverGood
>   SequentialDecisionProblems.CoreTheory.reward _ _ Increase (_, Good) =
>     one                       + one * increaseOverGood
>   SequentialDecisionProblems.CoreTheory.reward _ _ Freeze   (_,  Bad) =
>     one * badOverGood + one * freezeOverGood
>   SequentialDecisionProblems.CoreTheory.reward _ _ Increase (_,  Bad) =
>     one * badOverGood + one * increaseOverGood


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

and decidability of |Reachable|:

> SequentialDecisionProblems.TabBackwardsInduction.decidableReachable x = decidableUnit

Finally, we have to show that controls are finite

> -- finiteCtrl : {t : Nat} -> (x : State t) -> Finite (Ctrl t x)
> SequentialDecisionProblems.Utils.finiteCtrl _ = finiteFreezeOrIncrease

and, in order to use the fast, tail-recursive tabulated version of
backwards induction, that states are finite:

> SequentialDecisionProblems.TabBackwardsInduction.finiteState t =
>   finitePair (finiteFin) (finiteGoodOrBad)


* Optimal policies, optimal decisions, ...

We can now apply the results of our |CoreTheory| and of the |FullTheory|
to compute verified optimal policies, possible state-control sequences,
etc. To this end, we need to be able to show the outcome of the decision
process. This means implemeting functions to print states and controls:

> -- showState : {t : Nat} -> State t -> String
> SequentialDecisionProblems.Utils.showState {t} (e, Good) =
>   "(" ++ show (finToNat e) ++ ",Good)"
> SequentialDecisionProblems.Utils.showState {t} (e, Bad) =
>   "(" ++ show (finToNat e) ++ ",Bad)"

> -- showControl : {t : Nat} -> {x : State t} -> Ctrl t x -> String
> SequentialDecisionProblems.Utils.showCtrl {t} {x} Freeze = "Freeze"
> SequentialDecisionProblems.Utils.showCtrl {t} {x} Increase = "Increase"

>
> using implementation ShowNonNegDouble
> 
>   computation : { [STDIO] } Eff ()
>   computation =
>     do putStr ("enter number of steps:\n")
>        nSteps <- getNat
>        case (decidableViable {t = Z} nSteps (FZ, Good)) of
>          (Yes v) => do putStrLn ("computing optimal policies ...")
>                        -- ps   <- pure (backwardsInduction Z nSteps)
>                        ps   <- pure (tabTailRecursiveBackwardsInduction Z nSteps)
>                        putStrLn ("computing optimal controls ...")
>                        mxys <- pure (possibleStateCtrlSeqs (FZ, Good) () v ps)
>                        putStrLn "possible state-control sequences:"
>                        putStr "  "
>                        putStrLn (showlong mxys)
>                        mvs <- pure (possibleRewards' mxys)
>                        putStrLn "possible rewards:"
>                        putStr "  "
>                        putStrLn (show mvs)
>                        putStrLn ("done!")
>          (No _)  => putStrLn ("initial state non viable for " ++ cast {from = Int} (cast nSteps) ++ " steps")

> main : IO ()
> main = run computation


> {-

> ---}


-- Local Variables:
-- idris-packages: ("effects")
-- End:
