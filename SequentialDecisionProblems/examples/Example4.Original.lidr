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

> import SequentialDecisionProblems.examples.LeftAheadRight

> import SimpleProb.SimpleProb
> import SimpleProb.BasicOperations
> import SimpleProb.BasicProperties
> import SimpleProb.MonadicOperations
> import SimpleProb.MonadicProperties
> import SimpleProb.Measures
> import BoundedNat.BoundedNat
> import BoundedNat.Operations
> import BoundedNat.Properties
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
> import Void.Properties
> import Unit.Properties
> import Opt.Operations
> import Rel.TotalPreorder
> import LocalEffect.Exception
> import LocalEffect.StdIO

> -- %default total
> %auto_implicits off

> -- %logging 5

We reimplement "Example2.lidr", this time with |M = SimpleProb|.

* The monad M (SimpleProb):

** SimpleProb is a monad:

> SequentialDecisionProblems.CoreTheory.M = 
>   SimpleProb

> SequentialDecisionProblems.CoreTheory.fmap = 
>   SimpleProb.MonadicOperations.fmap

> SequentialDecisionProblems.Utils.ret = 
>   SimpleProb.MonadicOperations.ret

> SequentialDecisionProblems.Utils.bind = 
>   SimpleProb.MonadicOperations.bind

** M is a container monad:

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

** Reward function:

> SequentialDecisionProblems.CoreTheory.reward t x y (MkSigma c _) =
>   if c == Z
>   then (fromInteger 1)
>   else if (S c) == nColumns
>        then (fromInteger 2)
>        else (fromInteger 0)

** Measure:

> SequentialDecisionProblems.CoreTheory.meas = average
> SequentialDecisionProblems.FullTheory.measMon = monotoneAverage

** |Ctrl| is finite:

> SequentialDecisionProblems.Utils.finiteCtrl _ = 
>   finiteLeftAheadRight
> %freeze SequentialDecisionProblems.Utils.finiteCtrl

** Reachability

> SequentialDecisionProblems.CoreTheory.Reachable x' = Unit
> SequentialDecisionProblems.CoreTheory.reachableSpec1 {t} x r y = all (nexts t x y) where
>   all : (sp : SimpleProb  (State (S t))) -> SequentialDecisionProblems.CoreTheory.All (Reachable {t' = S t}) sp
>   all sp = all' (support sp) where
>     all' : (xs : List (State (S t))) -> Data.List.Quantifiers.All (Reachable {t' = S t}) xs
>     all' Nil = Nil
>     all' (x :: xs) = () :: (all' xs)

** Viability:

> SequentialDecisionProblems.CoreTheory.Viable n x = Unit

> SequentialDecisionProblems.CoreTheory.viableSpec1 {t} {n} x _ = MkSigma Ahead (ne, av) where
>   ne : SequentialDecisionProblems.CoreTheory.NotEmpty (nexts t x Ahead)
>   ne = nonEmptyLemma (nexts t x Ahead) 
>   av : SequentialDecisionProblems.CoreTheory.All (Viable {t = S t} n) (nexts t x Ahead)
>   av = [()]

> SequentialDecisionProblems.Utils.finiteViable n x = finiteUnit

> SequentialDecisionProblems.Utils.decidableViable n x = decidableUnit

** |cvalargmax| and |cvalmax| 

We want to implement |cvalmax|, |cvalargmax|, |cvalmaxSpec| and
|cvalargmaxSpec|. This can be easily done in terms of |Opt.max| and
|Opt.argmax| if we can show that

1) |LTE| is a *total* preorder 

2) |GoodCtrl t x n| is finite and, for every |t : Nat|, |x : State t|
   such that |Viable (S n) x|, its cardinality is not zero.

The first condition trivially holds, see
|NonNegRational.LTEProperties|. Finiteness and non-zero cardinality of
|GoodCtrl t x n|

< finiteGoodCtrl : {t : Nat} -> {n : Nat} -> 
<                  (x : State t) -> 
<                  Finite (GoodCtrl t x n) 

and

< cnzGoodCtrl : {t : Nat} -> {n : Nat} -> 
<               (x : State t) -> (v : Viable {t = t} (S n) x) ->
<               CardNotZ (finiteGoodCtrl {t} {n} x)

follow from finiteness of |Viable| (previous section ), finiteness of
|All|

> SequentialDecisionProblems.Utils.finiteAll = SimpleProb.MonadicProperties.finiteAll

, finiteness of |NotEmpty|

> SequentialDecisionProblems.Utils.finiteNotEmpty = SimpleProb.MonadicProperties.finiteNonEmpty

and finiteness of controls (see above). With these results in place, we have

> SequentialDecisionProblems.FullTheory.cvalmax {n} x r v ps =
>   Opt.Operations.max totalPreorderLTE (finiteGoodCtrl n x) (cardNotZGoodCtrl n x v) (cval x r v ps)

> SequentialDecisionProblems.CoreTheory.cvalargmax {n} x r v ps =
>   Opt.Operations.argmax totalPreorderLTE (finiteGoodCtrl n x) (cardNotZGoodCtrl n x v) (cval x r v ps)

> SequentialDecisionProblems.FullTheory.cvalmaxSpec {n} x r v ps =
>   Opt.Operations.maxSpec totalPreorderLTE (finiteGoodCtrl n x) (cardNotZGoodCtrl n x v) (cval x r v ps)

> SequentialDecisionProblems.FullTheory.cvalargmaxSpec {n} x r v ps =
>   Opt.Operations.argmaxSpec totalPreorderLTE (finiteGoodCtrl n x) (cardNotZGoodCtrl n x v) (cval x r v ps)


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
>      case (decidableViable {t = Z} nSteps x0) of
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
