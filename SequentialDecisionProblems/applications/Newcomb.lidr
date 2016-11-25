> module SequentialDecisionProblems.applications.Main

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

> import SimpleProb.SimpleProb
> import SimpleProb.BasicOperations
> import SimpleProb.BasicProperties
> import SimpleProb.MonadicOperations
> import SimpleProb.MonadicProperties
> import SimpleProb.Measures
> -- import BoundedNat.BoundedNat
> -- import BoundedNat.Operations
> -- import BoundedNat.Properties
> import SequentialDecisionProblems.examples.LeftAheadRight
> import Sigma.Sigma
> import Sigma.Operations
> import Sigma.Properties
> import Nat.LTProperties
> import NonNegRational.NonNegRational
> import NonNegRational.BasicOperations
> import NonNegRational.BasicProperties
> import NonNegRational.Predicates
> import NonNegRational.LTEProperties
> import Finite.Predicates
> import Finite.Operations
> import Finite.Properties
> import Unique.Predicates
> import Decidable.Predicates
> import Unit.Properties
> import Opt.Operations
> import Rel.TotalPreorder
> import LocalEffect.Exception
> import LocalEffect.StdIO
> import Fin.Operations
> import Pairs.Operations
> import Fraction.Fraction
> import Fraction.Normal
> import PNat.PNat
> import Nat.Positive
> import List.Operations
> import Fun.Operations

> -- %default total
> %auto_implicits off

> -- %logging 5

We specify Newcomb's problem as exemplified in [1] as a stochastic
sequential decision problem.

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

We model the problem as a stochastic SDP. At the first decision step,
the agent can pick up either the opaque box or both boxes. 

> data Choice = TakeOpaqueBox | TakeBothBoxes

> SequentialDecisionProblems.CoreTheory.Ctrl  Z    _ = Choice

In all subsequent decision steps, the agent has no relevant alternatives
 
> SequentialDecisionProblems.CoreTheory.Ctrl (S n) _ = Unit

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

> n   :  Nat
> n   =  99

> p1  :  NonNegRational
> p1  =  fromFraction (n, Element (S n) MkPositive)
> p2  :  NonNegRational
> p2  =  fromFraction (1, Element (S n) MkPositive)

We postulate that the sum of the probabilities of |[(x1, p1), (x2, p2)]|
and |[(x1, p2), (x2, p1)]| is one: 

> postulate sumOne1 : {t : Nat} -> {x1 : State t} -> {x2 : State t} -> 
>                     sumMapSnd [(x1, p1), (x2, p2)] = 1

> postulate sumOne2 : {t : Nat} -> {x1 : State t} -> {x2 : State t} -> 
>                     sumMapSnd [(x1, p2), (x2, p1)] = 1

This is in principle not necessary. But a naive implementation of
|sumOne1|

< sumOne1 = Refl

would take too long to type check. In fact, type checking |sumOne1|
would lead to a stack overflow. In oder to define the transition
function, we have to specify the kind of SDP at stake. Here, we have to
do with a stochastic SDP and therefore |M = SimpleProb|:

> SequentialDecisionProblems.CoreTheory.M = 
>   SimpleProb.SimpleProb
> SequentialDecisionProblems.CoreTheory.fmap =
>   SimpleProb.MonadicOperations.fmap
> SequentialDecisionProblems.Utils.ret =
>   SimpleProb.MonadicOperations.ret
> SequentialDecisionProblems.Utils.bind =
>   SimpleProb.MonadicOperations.bind

As it turns out, we also have to

> %freeze n
> %freeze fromFraction

to actuallly be able to use the postulates in the implementation of the
transition function. The alternative is, again, a stack overflow during
type checking. With these preliminaries in place, we can define the
transition function for Newcomb's problem. Selecting the opaque box at
decision step zero yields one million dollars in the opaque box with
probability |p1| and zero dollars with probability |p2| (with |p1 >>
p2|):

> SequentialDecisionProblems.CoreTheory.nexts Z () TakeOpaqueBox =
>   MkSimpleProb [(OneMillion, p1), (Zero, p2)] (sumOne1 {t = 1} {x1 = OneMillion} {x2 = Zero})

Conversely, selecting both boxes yields one million dollars in the
opaque box with probability |p2| and zero dollars with probability |p1|:

> SequentialDecisionProblems.CoreTheory.nexts Z () TakeBothBoxes =
>   MkSimpleProb [(OneMillion, p2), (Zero, p1)] (sumOne2 {t = 1} {x1 = OneMillion} {x2 = Zero})

At all subsequent decision steps, nothing interesting happens. There are
no options to decide upon and the transition function simply returns the
current state:

> SequentialDecisionProblems.CoreTheory.nexts (S n) s _ = SimpleProb.MonadicOperations.ret s

We can now procede to define the reward function for Newcomb's
problem. The return type of |reward| is |NonNegRational|

> SequentialDecisionProblems.CoreTheory.Val = NonNegRational.NonNegRational

for which we have a zero element

> SequentialDecisionProblems.CoreTheory.zero = fromInteger 0

an "addition" 

> SequentialDecisionProblems.CoreTheory.plus = NonNegRational.BasicOperations.plus

and a reflexive and transitive comparison relation

> SequentialDecisionProblems.CoreTheory.LTE = NonNegRational.Predicates.LTE
> SequentialDecisionProblems.FullTheory.reflexiveLTE = NonNegRational.LTEProperties.reflexiveLTE
> SequentialDecisionProblems.FullTheory.transitiveLTE = NonNegRational.LTEProperties.transitiveLTE

Moreover, addition preserves comparisons that is |a `LTE` b -> a + c
`LTE` b + c| for arbitary |a, b, c : NonNegRational|:

> SequentialDecisionProblems.FullTheory.monotonePlusLTE = NonNegRational.LTEProperties.monotonePlusLTE

Having fully characterized |Val|, the return type of the reward
function, we can now define the rewards for the first decision step in
units of 1k dollars

> SequentialDecisionProblems.CoreTheory.reward Z () TakeOpaqueBox OneMillion = 1000
> SequentialDecisionProblems.CoreTheory.reward Z () TakeOpaqueBox Zero       = 0
> SequentialDecisionProblems.CoreTheory.reward Z () TakeBothBoxes OneMillion = 1001
> SequentialDecisionProblems.CoreTheory.reward Z () TakeBothBoxes Zero       = 1

For all subsequent steps, rewards are simply zero:

> SequentialDecisionProblems.CoreTheory.reward (S n) _ _ _       = 0

Next, we have to show that |SimpleProb| is a container monad:

> SequentialDecisionProblems.CoreTheory.Elem = 
>   SimpleProb.MonadicOperations.Elem
> SequentialDecisionProblems.CoreTheory.NotEmpty = 
>   SimpleProb.MonadicOperations.NonEmpty
> SequentialDecisionProblems.CoreTheory.All = 
>   SimpleProb.MonadicOperations.All
> SequentialDecisionProblems.CoreTheory.elemNotEmptySpec0 = 
>   SimpleProb.MonadicProperties.elemNonEmptySpec0
> SequentialDecisionProblems.CoreTheory.elemNotEmptySpec1 = 
>   SimpleProb.MonadicProperties.elemNonEmptySpec1
> SequentialDecisionProblems.CoreTheory.tagElem = 
>   SimpleProb.MonadicOperations.tagElem
> SequentialDecisionProblems.CoreTheory.allElemSpec0 = 
>   SimpleProb.MonadicProperties.containerMonadSpec3

and explain how the decision maker accounts for uncertainties on rewards
induced by uncertainties in the transition function. We first assume
that the decision maker measures uncertain rewards by their average or,
in other words, expected value:

> SequentialDecisionProblems.CoreTheory.meas = average
> SequentialDecisionProblems.FullTheory.measMon = monotoneAverage



> {-



Notice that |SimpleProb|s are never empty. Thus, at every decision step,
there exists a control that yields non-empty next possible states

> nextsNonEmptyLemma : {t : Nat} -> 
>                      (x : State t) -> 
>                      SequentialDecisionProblems.CoreTheory.NotEmpty (nexts t x Ahead)
> nextsNonEmptyLemma {t} x = SequentialDecisionProblems.CoreTheory.elemNotEmptySpec0 {A = State (S t)} x sp xesp where
>   sp : SimpleProb (State (S t))  
>   sp = nexts t x Ahead
>   xesp : SequentialDecisionProblems.CoreTheory.Elem x sp
>   xesp = SimpleProb.MonadicProperties.containerMonadSpec1

We will take advantage of this fact for implementing |viableSpec1|








** M is measurable:



* Viable and Reachable

> -- Viable : (n : Nat) -> State t -> Type
> SequentialDecisionProblems.CoreTheory.Viable n x = Unit

> viableLemma : {t : Nat} -> {n : Nat} ->
>               (x : State t) -> 
>               SequentialDecisionProblems.CoreTheory.All (Viable {t = S t} n) (nexts t x Ahead)
> viableLemma (MkSigma n prf) = [()]

> -- viableSpec1 : (x : State t) -> Viable (S n) x -> GoodCtrl t x n
> SequentialDecisionProblems.CoreTheory.viableSpec1 {t} {n} x _ = MkSigma Ahead (ne, av) where
>   ne : SequentialDecisionProblems.CoreTheory.NotEmpty (nexts t x Ahead)
>   ne = nextsNonEmptyLemma {t} x
>   av : SequentialDecisionProblems.CoreTheory.All (Viable {t = S t} n) (nexts t x Ahead)
>   av = viableLemma x

> -- Reachable : State t' -> Type
> SequentialDecisionProblems.CoreTheory.Reachable x' = Unit

> -- reachableSpec1 : (x : State t) -> Reachable {t' = t} x -> (y : Ctrl t x) -> All (Reachable {t' = S t}) (nexts t x y)
> SequentialDecisionProblems.CoreTheory.reachableSpec1 {t} x r y = all (nexts t x y) where
>   all : (sp : SimpleProb  (State (S t))) -> SequentialDecisionProblems.CoreTheory.All (Reachable {t' = S t}) sp
>   all sp = all' (support sp) where
>     all' : (xs : List (State (S t))) -> Data.List.Quantifiers.All (Reachable {t' = S t}) xs
>     all' Nil = Nil
>     all' (x :: xs) = () :: (all' xs)


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
>                                    NonNegRational.LTEProperties.reflexiveLTE 
>                                    NonNegRational.LTEProperties.transitiveLTE 
>                                    NonNegRational.LTEProperties.totalLTE

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
> SequentialDecisionProblems.Helpers.finiteAll = SimpleProb.MonadicProperties.finiteAll

, finiteness of |Viable|

> -- finiteViable : {t : Nat} -> {n : Nat} -> 
> --                (x : State t) -> Finite (Viable {t} n x)
> SequentialDecisionProblems.Helpers.finiteViable _ = finiteUnit

, finiteness of |NotEmpty|

> -- finiteNonEmpty : {t : Nat} -> {n : Nat} -> 
> --                  (x : State t) -> (y : Ctrl t x) -> 
> --                  Finite (SequentialDecisionProblems.CoreTheory.NotEmpty (nexts t x y))
> SequentialDecisionProblems.Helpers.finiteNotEmpty {t} {n} x y = SimpleProb.MonadicProperties.finiteNonEmpty (nexts t x y)

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
> dViable {t} n x = Yes ()


* The computation:

> -- showState : {t : Nat} -> State t -> String
> SequentialDecisionProblems.Utils.showState = show

> -- showControl : {t : Nat} -> {x : State t} -> Ctrl t x -> String
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
>      case (dViable {t = Z} nSteps x0) of
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
>                       mxyvs <- pure (possibleStateCtrlSeqsRewards' mxys)
>                       putStrLn "possible state-control sequences and rewards:"
>                       putStr "  "
>                       putStrLn (show mxyvs)
>                       putStrLn "measure of possible rewards: "
>                       putStr "  "
>                       putStrLn (show (meas mvs))
>                       argmaxmax <- pure (argmaxMax {A = StateCtrlSeq Z nSteps} {B = Val} totalPreorderLTE (support mxyvs) (nonEmptyLemma mxyvs))
>                       putStrLn "best possible state-control sequence: "
>                       putStr "  "
>                       putStrLn (show (fst argmaxmax))
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


> ---}


[1] Stanford Encyclopedia of Phylosophy, Causal Decision Theory, 2010


-- Local Variables:
-- idris-packages: ("effects")
-- End:
 
