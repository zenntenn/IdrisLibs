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

> import SequentialDecisionProblems.examples.LeftAheadRight

> import FastSimpleProb.SimpleProb
> import FastSimpleProb.BasicOperations
> import FastSimpleProb.BasicProperties
> import FastSimpleProb.MonadicOperations
> import FastSimpleProb.MonadicProperties
> import FastSimpleProb.Measures
> import Sigma.Sigma
> import Sigma.Operations
> import Sigma.Properties
> import Nat.LTProperties
> import Double.Predicates
> import NonNegDouble.NonNegDouble
> import NonNegDouble.BasicOperations
> import NonNegDouble.BasicProperties
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

We specify Newcomb's problem as exemplified in [1]:

  "In Newcomb's problem, an agent may choose to take an opaque box or to
  take both the opaque box and a transparent one. The transparent box
  contains 1000 dollars that the agent plainly sees. The opaque box
  contains either nothing or one million dollars, depending on a
  prediction already made. The prediction was about the decision maker's
  choice. If the prediction was that the decision maker will take both
  boxes, then the opaque box is empty. On the other hand, if the
  prediction was that the agent will take just the opaque box, then the
  opaque box contains a million dollars. The prediction is reliable. The
  agent knows all these features of his decision problem."

as a stochastic sequential decision problem. Thus, even though we are
only interested in a single decision step, we have to define states,
controls and the transition and reward functions for an arbitrary number
of steps. We start with controls.


* Controls

At the first decision step, the agent can pick up either the opaque box
or both boxes:

> data Choice = TakeOpaqueBox | TakeBothBoxes

> SequentialDecisionProblems.CoreTheory.Ctrl  Z    _ = Choice

In all subsequent decision steps, the agent has no relevant alternatives
 
> SequentialDecisionProblems.CoreTheory.Ctrl (S n) _ = Unit

For reasons that will become clear in section "Completing the problem
specification" below, it is useful to show that |Choice| is finite. This
means that there is a one-to-one correspondence between |Choice| and
|Fin 2|:

> to : Choice -> Fin 2
> to TakeOpaqueBox =    FZ
> to TakeBothBoxes = FS FZ

> from : Fin 2 -> Choice
> from             FZ   = TakeOpaqueBox
> from         (FS FZ)  = TakeBothBoxes
> from     (FS (FS  k)) = absurd k

> toFrom : (k : Fin 2) -> to (from k) = k
> toFrom             FZ   = Refl
> toFrom         (FS FZ)  = Refl
> toFrom     (FS (FS  k)) = absurd k

> fromTo : (a : Choice) -> from (to a) = a
> fromTo TakeOpaqueBox  = Refl
> fromTo TakeBothBoxes = Refl

> finiteChoice : Finite Choice
> finiteChoice = MkSigma 2 (MkIso to from toFrom fromTo)

It will also be useful to know that |Choice| is non empty:

> cardNotZChoice : CardNotZ finiteChoice
> cardNotZChoice = cardNotZLemma finiteChoice TakeOpaqueBox


* States

The states that the agent can observe are similarly trivial. At the
first decision step, the agent can see 1000 dollars in the transparent
box but not the content of the opaque box. After the decision has been
made, he can see the content of the opaque box which can be empty of
contain one million dollars:

> data OpaqueBoxContent = Zero | OneMillion

> SequentialDecisionProblems.CoreTheory.State  Z    = Unit
> SequentialDecisionProblems.CoreTheory.State (S n) = OpaqueBoxContent

The agent knows that his choices are predicted reliably. This means
that, if he picks up the opaque box only, there is a high probability
that it contains one million dollars. Similarly, if he chooses both
boxes, the opaque box will likely be empty. Let |p1| be the probability
that the prediction is right and |p2| the probability that it is wrong
with |p1 >> p2|:

> p   :  Double
> p   =  99

> p1  :  NonNegDouble
> p1  =  Element (p   / (p + 1.0)) (MkNonNegative Oh)
> p2  :  NonNegDouble
> p2  =  Element (1.0 / (p + 1.0)) (MkNonNegative Oh)


* Transition function

Selecting the opaque box at decision step zero yields one million
dollars in the opaque box with probability |p1| and zero dollars with
probability |p2| (with |p1 >> p2|):

> SequentialDecisionProblems.CoreTheory.nexts Z () TakeOpaqueBox =
>   MkSimpleProb [(OneMillion, p1), (Zero, p2)] (MkPositive Oh)

Conversely, selecting both boxes yields one million dollars in the
opaque box with probability |p2| and zero dollars with probability |p1|:

> SequentialDecisionProblems.CoreTheory.nexts Z () TakeBothBoxes =
>   MkSimpleProb [(OneMillion, p2), (Zero, p1)] (MkPositive Oh)

At all subsequent decision steps, nothing interesting happens. There are
no options to decide upon and the transition function simply returns the
current state:

> SequentialDecisionProblems.CoreTheory.nexts (S n) s _ = FastSimpleProb.MonadicOperations.ret s


* |Val| and |LTE|:

> SequentialDecisionProblems.CoreTheory.Val = 
>   NonNegDouble.NonNegDouble

> SequentialDecisionProblems.CoreTheory.plus = 
>   NonNegDouble.BasicOperations.plus

> SequentialDecisionProblems.CoreTheory.zero = 
>   fromInteger 0

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

We can now define the reward function for Newcomb's problem. We measure
rewards in units of millions of dollars

> oneMillion : NonNegDouble
> oneMillion = Element 1.0 (MkNonNegative Oh)

> oneThousand : NonNegDouble
> oneThousand = Element 0.001 (MkNonNegative Oh)

> SequentialDecisionProblems.CoreTheory.reward Z () TakeOpaqueBox OneMillion = oneMillion
> SequentialDecisionProblems.CoreTheory.reward Z () TakeOpaqueBox Zero       =       zero
> SequentialDecisionProblems.CoreTheory.reward Z () TakeBothBoxes OneMillion = oneMillion + oneThousand
> SequentialDecisionProblems.CoreTheory.reward Z () TakeBothBoxes Zero       =       zero + oneThousand

For all subsequent steps, rewards are simply zero:

> SequentialDecisionProblems.CoreTheory.reward (S n) _ _ _       = zero


* Completing the problem specification

To be able to apply the verified, generic backwards induction algorithm
of |CoreTheory| to compute optimal policies for Newcomb's problem, we
have to explain how the decision maker accounts for uncertainties on
rewards induced by uncertainties in the transition function. We first
assume that the decision maker measures uncertain rewards by their
average or, in other words, expected value:

> SequentialDecisionProblems.CoreTheory.meas = worst -- expectedValue
> SequentialDecisionProblems.FullTheory.measMon = monotoneWorst -- monotoneExpectedValue

Further on, we have to implement the notions of viability and
reachability. We start by positing that all states are viable for any
number of steps:

> -- Viable : (n : Nat) -> State t -> Type
> SequentialDecisionProblems.CoreTheory.Viable n x = Unit

From this definition, it trivially follows that all elements of an
arbitrary list of states are viable for an arbitrary number of steps:

> viableLemma : {t, n : Nat} -> (xs : List (State t)) -> All (Viable n) xs
> viableLemma  Nil      = Nil
> viableLemma (x :: xs) = () :: (viableLemma xs)

This fact and the (less trivial) result that simple probability
distributions are never empty, see |nonEmptyLemma| in
|MonadicProperties| in |SimpleProb|, allows us to show that the above
definition of |Viable| fulfills |viableSpec1|:

> -- viableSpec1 : (x : State t) -> Viable (S n) x -> GoodCtrl t x 
> SequentialDecisionProblems.CoreTheory.viableSpec1 {t = Z} {n} () v = 
>   MkSigma TakeOpaqueBox (ne, av) where
>     ne : SequentialDecisionProblems.CoreTheory.NotEmpty (nexts Z () TakeOpaqueBox)
>     ne = nonEmptyLemma (nexts Z () TakeOpaqueBox)
>     av : SequentialDecisionProblems.CoreTheory.All (Viable {t = S Z} n) (nexts Z () TakeOpaqueBox)
>     av = viableLemma {t = S Z} (support (nexts Z () TakeOpaqueBox))
> SequentialDecisionProblems.CoreTheory.viableSpec1 {t = S m} {n} x v = 
>   MkSigma () (ne, av) where
>     ne : SequentialDecisionProblems.CoreTheory.NotEmpty (nexts (S m) x ())
>     ne = nonEmptyLemma (nexts (S m) x ())
>     av : SequentialDecisionProblems.CoreTheory.All (Viable {t = S (S m)} n) (nexts (S m) x ())
>     av = viableLemma {t = S (S m)} (support (nexts (S m) x ()))

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
> SequentialDecisionProblems.Utils.finiteCtrl {t = Z}   _ = finiteChoice
> SequentialDecisionProblems.Utils.finiteCtrl {t = S m} _ = finiteUnit


* Optimal policies, optimal decisions, ...

With Necomb's problem fully specified as a SDP, we can apply the results
of our |CoreTheory| and of the |FullTheory| to compute verified optimal
policies, possible state-control sequences, etc.

The interesting question is whether the decision maker will pick up only
the opaque box or both boxes at the first decision step. All following
decisions should be immaterial. Still, we want to assess that we get
consistent results no matter how many decision steps we do. To this end,
we need to be able to show the outcome of the decision process. This
means implemeting functions to print states and controls:

> -- showState : {t : Nat} -> State t -> String
> SequentialDecisionProblems.Utils.showState {t = Z}  ()          = ""
> SequentialDecisionProblems.Utils.showState {t = S n} Zero       = "0"
> SequentialDecisionProblems.Utils.showState {t = S n} OneMillion = "1"

> -- showControl : {t : Nat} -> {x : State t} -> Ctrl t x -> String
> SequentialDecisionProblems.Utils.showCtrl {t = Z}   {x = ()} TakeOpaqueBox = "Take opaque box"
> SequentialDecisionProblems.Utils.showCtrl {t = Z}   {x = ()} TakeBothBoxes = "Take both boxes"
> SequentialDecisionProblems.Utils.showCtrl {t = S n} {x}      ()            = ""

> computation : { [STDIO] } Eff ()
> computation =
>   do putStr ("enter number of steps:\n")
>      nSteps <- getNat
>      case (decidableViable {t = Z} nSteps ()) of
>        (Yes v) => do putStrLn ("computing optimal policies ...")
>                      ps   <- pure (backwardsInduction Z nSteps)
>                      putStrLn ("computing optimal controls ...")
>                      mxys <- pure (possibleStateCtrlSeqs () () v ps)
>                      putStrLn "possible state-control sequences:"
>                      putStr "  "
>                      putStrLn (show mxys)
>                      mvs <- pure (possibleRewards' mxys)
>                      putStrLn "possible rewards:"
>                      putStr "  "
>                      putStrLn (show mvs)
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


> ---}


[1] Stanford Encyclopedia of Phylosophy, Causal Decision Theory, 2010


-- Local Variables:
-- idris-packages: ("effects")
-- End:
 
