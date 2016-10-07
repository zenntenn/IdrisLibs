> module SequentialDecisionProblems.Generic.Main

> import Decidable.Order

> import Data.Fin
> import Data.Vect
> import Data.So
> import Control.Monad.Identity
> import Control.Isomorphism
> import Effects
> import Effect.Exception
> import Effect.StdIO
> import Syntax.PreorderReasoning

> import SequentialDecisionProblems.Generic.CoreTheory
> import SequentialDecisionProblems.Generic.FullTheory
> import SequentialDecisionProblems.Generic.Utils
> import SequentialDecisionProblems.Generic.Helpers

> import Identity.Operations
> import Identity.Properties
> import BoundedNat.BoundedNat
> import BoundedNat.Operations
> import BoundedNat.Properties
> import SequentialDecisionProblems.Generic.LeftAheadRight
> import Sigma.Sigma
> import Sigma.Operations
> import Sigma.Properties
> import Nat.LTEProperties
> import Nat.LTProperties
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

> -- %default total
> %auto_implicits off




The possibly simplest "cylinder" problem. |M| is the identity monad, the
state space is constant and we can move to the left, ahead or to the
right as we wish.



* The monad M (Identity):


** M is a monad:

> SequentialDecisionProblems.Generic.CoreTheory.M = Identity
> SequentialDecisionProblems.Generic.CoreTheory.fmap = map {f = Identity}

> SequentialDecisionProblems.Generic.Utils.ret = pure
> SequentialDecisionProblems.Generic.Utils.bind = (>>=)

** M is a container monad:

> SequentialDecisionProblems.Generic.CoreTheory.Elem = Identity.Operations.Elem
> SequentialDecisionProblems.Generic.CoreTheory.NotEmpty = Identity.Operations.NonEmpty
> SequentialDecisionProblems.Generic.CoreTheory.All = Identity.Operations.All
> SequentialDecisionProblems.Generic.CoreTheory.elemNotEmptySpec0 = Identity.Properties.elemNonEmptySpec0
> SequentialDecisionProblems.Generic.CoreTheory.elemNotEmptySpec1 = Identity.Properties.elemNonEmptySpec1
> SequentialDecisionProblems.Generic.CoreTheory.tagElem = Identity.Operations.tagElem
> -- SequentialDecisionProblems.Generic.CoreTheory.containerMonadSpec3 {A} {P} a1 (Id a2) pa2 a1eqa2 =
> SequentialDecisionProblems.Generic.CoreTheory.allElemSpec0 {A} {P} a1 (Id a2) pa2 a1eqa2 =
>   replace (sym a1eqa2) pa2

* The decision process:

> maxColumn : Nat
> maxColumn = 10

> nColumns : Nat
> nColumns = S maxColumn



** States:

> SequentialDecisionProblems.Generic.CoreTheory.State t = LTB nColumns


** Controls:

> SequentialDecisionProblems.Generic.CoreTheory.Ctrl t x = LeftAheadRight

** Transition function:

> SequentialDecisionProblems.Generic.CoreTheory.nexts t (MkSigma Z prf) Left =
>   Id (MkSigma maxColumn (ltIdS maxColumn))
> SequentialDecisionProblems.Generic.CoreTheory.nexts t (MkSigma (S n) prf) Left =
>   Id (MkSigma n (ltLemma1 n nColumns prf))
> SequentialDecisionProblems.Generic.CoreTheory.nexts t (MkSigma n prf) Ahead =
>   Id (MkSigma n prf)
> SequentialDecisionProblems.Generic.CoreTheory.nexts t (MkSigma n prf) Right with (decLT n maxColumn)
>   | (Yes p)     = Id (MkSigma (S n) (LTESucc p))
>   | (No contra) = Id (MkSigma  Z    (LTESucc LTEZero))

** Reward function:

> SequentialDecisionProblems.Generic.CoreTheory.Val = Nat

> SequentialDecisionProblems.Generic.CoreTheory.reward t x y (MkSigma c _) =
>   if c == Z
>   then (S Z)
>   else if (S c) == nColumns
>        then (S (S Z))
>        else Z

> SequentialDecisionProblems.Generic.CoreTheory.plus = Prelude.Nat.plus
> SequentialDecisionProblems.Generic.CoreTheory.zero = Z

> SequentialDecisionProblems.Generic.CoreTheory.LTE = Prelude.Nat.LTE
> SequentialDecisionProblems.Generic.FullTheory.reflexiveLTE = Nat.LTEProperties.reflexiveLTE
> SequentialDecisionProblems.Generic.FullTheory.transitiveLTE = Nat.LTEProperties.transitiveLTE

> SequentialDecisionProblems.Generic.FullTheory.monotonePlusLTE = Nat.LTEProperties.monotoneNatPlusLTE

** M is measurable:

> SequentialDecisionProblems.Generic.CoreTheory.meas (Id x) = x
> SequentialDecisionProblems.Generic.FullTheory.measMon f g prf (Id x) = prf x

* Viable and Reachable

> -- Viable : (n : Nat) -> State t -> Type
> SequentialDecisionProblems.Generic.CoreTheory.Viable n x =  Unit

> -- viableSpec1 : (x : State t) -> Viable (S n) x -> GoodCtrl t x n
> SequentialDecisionProblems.Generic.CoreTheory.viableSpec1 {t} x v = MkSigma Left (nonEmptyLemma (nexts t x Left), ())

> -- Reachable : State t' -> Type
> SequentialDecisionProblems.Generic.CoreTheory.Reachable x' = Unit

> -- reachableSpec1 : (x : State t) -> Reachable {t' = t} x -> (y : Ctrl t x) -> All (Reachable {t' = S t}) (nexts t x y)
> SequentialDecisionProblems.Generic.CoreTheory.reachableSpec1 x r y = ()


* Max and argmax

We want to implement |max|, |argmax|, |maxSpec| and |argmaxSpec|. This
can be easily done in terms of |Opt.max| and |Opt.argmax| if we can show
that 

1) |LTE| is a *total* preorder 

2) |GoodCtrl t x n| is finite and, for every |t : Nat|, |x : State t|
   such that |Viable (S n) x|, its cardinality is not zero.

The first condition trivially holds 

> totalPreorderLTE : TotalPreorder Val
> totalPreorderLTE = MkTotalPreorder SequentialDecisionProblems.Generic.CoreTheory.LTE 
>                                    Nat.LTEProperties.reflexiveLTE 
>                                    Nat.LTEProperties.transitiveLTE 
>                                    Nat.LTEProperties.totalLTE

Finiteness and non-zero cardinality of |GoodCtrl t x n|

< finiteGoodCtrl : {t : Nat} -> {n : Nat} -> 
<                  (x : State t) -> 
<                  Finite (GoodCtrl t x n) 

< cnzGoodCtrl : {t : Nat} -> {n : Nat} -> 
<               (x : State t) -> (v : Viable {t = t} (S n) x) ->
<               CardNotZ (finiteGoodCtrl {t} {n} x)

follow from finiteness of |All|

> -- finiteAll : {A : Type} -> {P : A -> Type} -> 
> --             Finite1 P -> (ma : M A) -> Finite (All P ma)
> SequentialDecisionProblems.Generic.Helpers.finiteAll = Identity.Properties.finiteAll

, finiteness of |Viable|

> -- finiteViable : {t : Nat} -> {n : Nat} -> 
> --                (x : State t) -> Finite (Viable {t} n x)
> SequentialDecisionProblems.Generic.Helpers.finiteViable _ = finiteUnit

, finiteness of |NonEmpty|

> -- finiteNonEmpty : {t : Nat} -> {n : Nat} -> 
> --                  (x : State t) -> (y : Ctrl t x) -> 
> --                  Finite (SequentialDecisionProblems.Generic.CoreTheory.NotEmpty (nexts t x y))
> SequentialDecisionProblems.Generic.Helpers.finiteNotEmpty {t} {n} x y = Identity.Properties.finiteNonEmpty (nexts t x y)

and, finally, finiteness of controls

> -- finiteCtrl : {t : Nat} -> {n : Nat} -> (x : State t) -> Finite (Ctrl t x) 
> SequentialDecisionProblems.Generic.Helpers.finiteCtrl _ = finiteLeftAheadRight
> %freeze SequentialDecisionProblems.Generic.Helpers.finiteCtrl

With these results in place, we have

> SequentialDecisionProblems.Generic.FullTheory.cvalmax x r v ps =
>   Opt.Operations.max totalPreorderLTE (finiteGoodCtrl x) (cardNotZGoodCtrl x v) (cval x r v ps)

> SequentialDecisionProblems.Generic.CoreTheory.cvalargmax x r v ps =
>   Opt.Operations.argmax totalPreorderLTE (finiteGoodCtrl x) (cardNotZGoodCtrl x v) (cval x r v ps)

> SequentialDecisionProblems.Generic.FullTheory.cvalmaxSpec x r v ps =
>   Opt.Operations.maxSpec totalPreorderLTE (finiteGoodCtrl x) (cardNotZGoodCtrl x v) (cval x r v ps)

> SequentialDecisionProblems.Generic.FullTheory.cvalargmaxSpec x r v ps =
>   Opt.Operations.argmaxSpec totalPreorderLTE (finiteGoodCtrl x) (cardNotZGoodCtrl x v) (cval x r v ps)


* Decidability of Viable

> dViable : {t : Nat} -> (n : Nat) -> (x : State t) -> Dec (Viable {t} n x)
> dViable n x = Yes ()

* The computation:

> -- showState : {t : Nat} -> State t -> String
> SequentialDecisionProblems.Generic.Utils.showState = show

> -- showControl : {t : Nat} -> {x : State t} -> Ctrl t x -> String
> SequentialDecisionProblems.Generic.Utils.showCtrl = show

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
>                       putStrLn (show mxys)
>                       putStrLn ("done!")                       
>        (No _)   => putStrLn ("initial column non viable for " ++ cast {from = Int} (cast nSteps) ++ " steps")

> main : IO ()
> main = run computation

> {-

> ---}
