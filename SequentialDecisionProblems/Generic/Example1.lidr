> module Main

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
> -- import SeqDecProbsUtils
> -- import SeqDecProbsHelpers

> import Identity.Operations
> import Identity.Properties
> import BoundedNat.BoundedNat
> import BoundedNat.Operations
> import BoundedNat.Properties
> -- import SequentialDecisionProblems.Generic.LeftAheadRight
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
> -- import Opt
> import Rel.TotalPreorder
> import LocalEffect.Exception
> import LocalEffect.StdIO
> import Fin.Operations
> import Pairs.Operations

> %default total
> %auto_implicits off




The possibly simplest "cylinder" problem. |M| is the identity monad, the
state space is constant and we can move to the left, ahead or to the
right as we wish.



* The monad M (Identity):


** M is a monad:

> CoreTheory.M = Identity
> CoreTheory.fmap = map
> CoreTheory.ret = return
> CoreTheory.bind = (>>=)


** M is a container monad:

> CoreTheory.Elem = IdentityOperations.Elem
> CoreTheory.NonEmpty = IdentityOperations.NonEmpty
> CoreTheory.All = IdentityOperations.All
> CoreTheory.elemNonEmptySpec0 = IdentityProperties.elemNonEmptySpec0
> CoreTheory.elemNonEmptySpec1 = IdentityProperties.elemNonEmptySpec1
> CoreTheory.tagElem = IdentityOperations.tagElem
> CoreTheory.containerMonadSpec3 {A} {P} a1 (Id a2) pa2 a1eqa2 =
>   replace (sym a1eqa2) pa2


* The decision process:

> maxColumn : Nat
> maxColumn = 10

> nColumns : Nat
> nColumns = S maxColumn

> {-

** States:

> CoreTheory.State t = LTB nColumns


** Controls:

> CoreTheory.Ctrl t x = LeftAheadRight


** Transition function:

> CoreTheory.step t (MkSigma Z prf) Left =
>   Id (MkSigma maxColumn (ltIdS maxColumn))
> CoreTheory.step t (MkSigma (S n) prf) Left =
>   Id (MkSigma n (ltLemma1 n nColumns prf))
> CoreTheory.step t (MkSigma n prf) Ahead =
>   Id (MkSigma n prf)
> CoreTheory.step t (MkSigma n prf) Right with (decLT n maxColumn)
>   | (Yes p)     = Id (MkSigma (S n) (LTESucc p))
>   | (No contra) = Id (MkSigma  Z    (LTESucc LTEZero))


** Reward function:

> CoreTheory.Val = Nat

> CoreTheory.reward t x y (MkSigma c _) =
>   if c == Z
>   then (S Z)
>   else if (S c) == nColumns
>        then (S (S Z))
>        else Z

> CoreTheory.plus = Prelude.Nat.plus
> CoreTheory.zero = Z

> CoreTheory.LTE = Prelude.Nat.LTE
> CoreTheory.reflexiveLTE = NatLTEProperties.reflexiveLTE
> CoreTheory.transitiveLTE = NatLTEProperties.transitiveLTE

> CoreTheory.monotonePlusLTE = NatLTEProperties.monotoneNatPlusLTE

** M is measurable:

> CoreTheory.meas (Id x) = x
> CoreTheory.measMon f g prf (Id x) = prf x


* Viable and Reachable

> -- Viable : (n : Nat) -> State t -> Type
> CoreTheory.Viable n x =  Unit

> -- viableSpec1 : (x : State t) -> Viable (S n) x -> GoodCtrl t x n
> CoreTheory.viableSpec1 {t} x v = MkSigma Left (nonEmptyLemma (step t x Left), ())

> -- Reachable : State t' -> Type
> CoreTheory.Reachable x' = Unit

> -- reachableSpec1 : (x : State t) -> Reachable {t' = t} x -> (y : Ctrl t x) -> All (Reachable {t' = S t}) (step t x y)
> CoreTheory.reachableSpec1 x r y = ()



* Max and argmax

We want to implement |max|, |argmax|, |maxSpec| and |argmaxSpec|. This
can be easily done in terms of |Opt.max| and |Opt.argmax| if we can show
that 

1) |LTE| is a *total* preorder 

2) |GoodCtrl t x n| is finite and, for every |t : Nat|, |x : State t|
   such that |Viable (S n) x|, its cardinality is not zero.

The first condition trivially holds 

> totalPreorderLTE : TotalPreorder Val
> totalPreorderLTE = MkTotalPreorder CoreTheory.LTE 
>                                    NatLTEProperties.reflexiveLTE 
>                                    NatLTEProperties.transitiveLTE 
>                                    NatLTEProperties.totalLTE

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
> SeqDecProbsHelpers.finiteAll = IdentityProperties.finiteAll

, finiteness of |Viable|

> -- finiteViable : {t : Nat} -> {n : Nat} -> 
> --                (x : State t) -> Finite (Viable {t} n x)
> SeqDecProbsHelpers.finiteViable _ = finiteUnit

, finiteness of |NonEmpty|

> -- finiteNonEmpty : {t : Nat} -> {n : Nat} -> 
> --                  (x : State t) -> (y : Ctrl t x) -> 
> --                  Finite (CoreTheory.NonEmpty (step t x y))
> SeqDecProbsHelpers.finiteNonEmpty {t} {n} x y = IdentityProperties.finiteNonEmpty (step t x y)

and, finally, finiteness of controls

> -- finiteCtrl : {t : Nat} -> {n : Nat} -> (x : State t) -> Finite (Ctrl t x) 
> SeqDecProbsHelpers.finiteCtrl _ = finiteLeftAheadRight
> %freeze SeqDecProbsHelpers.finiteCtrl

With these results in place, we have

> CoreTheory.max x v =
>   Opt.max totalPreorderLTE (finiteGoodCtrl x) (cardNotZGoodCtrl x v)

> CoreTheory.argmax x v  =
>   Opt.argmax totalPreorderLTE (finiteGoodCtrl x) (cardNotZGoodCtrl x v)

> CoreTheory.maxSpec x v =
>   Opt.maxSpec totalPreorderLTE (finiteGoodCtrl x) (cardNotZGoodCtrl x v)

> CoreTheory.argmaxSpec x v =
>   Opt.argmaxSpec totalPreorderLTE (finiteGoodCtrl x) (cardNotZGoodCtrl x v)



* Decidability of Viable

> dViable : {t : Nat} -> (n : Nat) -> (x : State t) -> Dec (Viable {t} n x)
> dViable n x = Yes ()



* The computation:

> -- showState : {t : Nat} -> State t -> String
> SeqDecProbsUtils.showState = show

> -- showControl : {t : Nat} -> {x : State t} -> Ctrl t x -> String
> SeqDecProbsUtils.showCtrl = show

> computation : { [STDIO] } Eff ()
> computation =
>   do putStr ("enter number of steps:\n")
>      nSteps <- getNat
>      putStr ("enter initial column:\n")
>      x0 <- getLTB nColumns
>      case (dViable {t = Z} nSteps x0) of
>        (Yes v0) => do putStrLn ("computing optimal policies ...")
>                       ps   <- pure (bi Z nSteps)
>                       putStrLn ("computing optimal controls ...")
>                       mxys <- pure (possibleStateCtrlSeqs x0 () v0 ps)
>                       putStrLn (show mxys)
>                       putStrLn ("done!")                       
>        (No _)   => putStrLn ("initial column non viable for " ++ cast {from = Int} (cast nSteps) ++ " steps")

> main : IO ()
> main = run computation

> ---}
