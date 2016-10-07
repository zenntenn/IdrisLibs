> module SequentialDecisionProblems.Generic.Utils

> import Data.Fin
> import Control.Isomorphism

> import SequentialDecisionProblems.Generic.CoreTheory
> import Sigma.Sigma
> import Sigma.Operations
> import Finite.Predicates
> import Fun.Operations

> %default total
> %access public export
> %auto_implicits off


* ...

> |||
> FiniteViable : Type
> FiniteViable = {t : Nat} -> {n : Nat} -> (x : State t) -> Finite (Viable {t} n x)

> |||
> FiniteAll : Type
> FiniteAll = {A : Type} -> {P : A -> Type} -> Finite1 P -> (ma : M A) -> Finite (All P ma)

> |||
> FiniteAllViable : Type
> FiniteAllViable = {t : Nat} -> {n : Nat} -> 
>                   (x : State t) -> (y : Ctrl t x) -> 
>                   Finite (All (Viable {t = S t} n) (nexts t x y))

> |||
> FiniteNonEmpty : Type
> FiniteNonEmpty = {t : Nat} -> {n : Nat} -> 
>                  (x : State t) -> (y : Ctrl t x) -> 
>                  Finite (NotEmpty (nexts t x y))

> |||
> FiniteGoodCtrl : Type
> FiniteGoodCtrl = {t : Nat} -> {n : Nat} -> 
>                  (x : State t) -> Viable {t = t} (S n) x ->
>                  Finite (GoodCtrl t x n) 

> {-
> finiteAllViable : FiniteAll -> FiniteViable -> FiniteAllViable
> finiteAllViable fAll fViable = fAllViable where
>   fAll' : {A : Type} -> {P : A -> Type} -> Finite1 P -> (ma : M A) -> Finite (All P ma)
>   fAll' = fAll
>   fViable' : {t : Nat} -> {n : Nat} -> (x : State t) -> Finite (Viable {t} n x)
>   fViable' = fViable
>   fAllViable : {t : Nat} -> {n : Nat} -> 
>                (x : State t) -> (y : Ctrl t x) -> 
>                Finite (All (Viable {t = S t} n) (nexts t x y))
>   fAllViable {t} {n} x y = fAll' (fViable' {t = S t} {n}) (nexts t x y)
> -}

* Show states and controls

> |||
> showState : {t : Nat} -> State t -> String

> |||
> showCtrl : {t : Nat} -> {x : State t} -> Ctrl t x -> String

> |||
> showStateCtrl : {t : Nat} -> Sigma (State t) (Ctrl t) -> String
> showStateCtrl {t} (MkSigma x y) = "(" ++ showState {t} x ++ " ** " ++ showCtrl {t} {x} y ++ ")"


* Sequences of state-control pairs

> ||| 
> data StateCtrlSeq : (t : Nat) -> (n : Nat) -> Type where
>   Nil   :  {t : Nat} -> (x : State t) -> StateCtrlSeq t Z
>   (::)  :  {t, n : Nat} -> Sigma (State t) (Ctrl t) -> StateCtrlSeq (S t) n -> StateCtrlSeq t (S n)

> using (t : Nat, n : Nat)
>   implementation Show (StateCtrlSeq t n) where
>     show = show' where
>       show' : {t : Nat} -> {n : Nat} -> StateCtrlSeq t n -> String
>       show' xys = "[" ++ show'' "" xys ++ "]" where
>         show'' : {t' : Nat} -> {n' : Nat} -> String -> StateCtrlSeq t' n' -> String
>         show'' {t'} {n' =   Z}      acc (Nil x)      =
>           acc ++ "(" ++ showState x ++ " ** " ++ " " ++ ")" 
>         show'' {t'} {n' = S m'} acc (xy :: xys)    = 
>           show'' {t' = S t'} {n' = m'} (acc ++ showStateCtrl xy ++ ", ") xys

> |||
> valStateCtrlSeq : (t : Nat) -> (n : Nat) -> StateCtrlSeq t n -> Val
> valStateCtrlSeq t       Z   (Nil x) = 
>   zero
> valStateCtrlSeq t    (S Z)  ((MkSigma x y) :: (Nil x')) = 
>   reward t x y x'
> valStateCtrlSeq t (S (S m)) ((MkSigma x y) :: (MkSigma x' y') :: xys) = 
>   reward t x y x' `plus` valStateCtrlSeq (S t) (S m) ((MkSigma x' y') :: xys)


* Trajectories

> ||| The monadic operations
> ret   :  {A : Type} -> A -> M A
> bind  :  {A, B : Type} -> M A -> (A -> M B) -> M B
> postulate monadSpec1   :  {A, B : Type} -> {f : A -> B} ->
>                           (fmap f) . ret = ret . f
> postulate monadSpec21  :  {A, B : Type} -> {f : A -> M B} -> {a : A} ->
>                           bind (ret a) f = f a
> postulate monadSpec22  :  {A : Type} -> {ma : M A} ->
>                           bind ma ret = ma
> postulate monadSpec23  :  {A, B, C : Type} -> {f : A -> M B} -> {g : B -> M C} -> {ma : M A} ->
>                           bind (bind ma f) g = bind ma (\ a => bind (f a) g)

> |||
> possibleStateCtrlSeqs  :  {t, n : Nat} -> (x : State t) -> (r : Reachable x) -> (v : Viable n x) ->
>                           (ps : PolicySeq t n) -> M (StateCtrlSeq t n)
> possibleStateCtrlSeqs {t} {n = Z}    x r v Nil         =  ret (Nil x)
> possibleStateCtrlSeqs {t} {n = S m}  x r v (p :: ps')  =
>   fmap g (bind (tagElem mx') f) where
>     y   :  Ctrl t x
>     y   =  ctrl (p x r v)
>     mx' :  M (State (S t))
>     mx' =  nexts t x y
>     av  :  All (Viable m) mx'
>     av  =  allViable (p x r v)
>     g   :  StateCtrlSeq (S t) m -> StateCtrlSeq t (S m)
>     g   =  ((MkSigma x y) ::)
>     f   :  Sigma (State (S t)) (\ x' => x' `Elem` mx') -> M (StateCtrlSeq (S t) m)
>     f (MkSigma x' x'emx') = possibleStateCtrlSeqs {n = m} x' r' v' ps' where
>       ar  :  All Reachable mx'
>       ar  =  reachableSpec1 x r y
>       r'  :  Reachable x'
>       r'  =  allElemSpec0 x' mx' ar x'emx'
>       v'  :  Viable m x'
>       v'  =  allElemSpec0 x' mx' av x'emx'

> |||
> possibleStateCtrlSeqsRewards : {t : Nat} -> {n : Nat} -> 
>                                (x : State t) -> (r : Reachable x) -> (v : Viable n x) ->
>                                (ps : PolicySeq t n) -> M (StateCtrlSeq t n, Val)
> possibleStateCtrlSeqsRewards {t} {n} x r v ps = 
>   fmap (pair (id, valStateCtrlSeq t n)) (possibleStateCtrlSeqs {t} {n} x r v ps)

> |||
> possibleStateCtrlSeqsRewards' : {t : Nat} -> {n : Nat} -> 
>                                 M (StateCtrlSeq t n) -> M (StateCtrlSeq t n, Val)
> possibleStateCtrlSeqsRewards' {t} {n} xys = fmap (pair (id, valStateCtrlSeq t n)) xys

> |||
> possibleRewards : {t : Nat} -> {n : Nat} -> 
>                   (x : State t) -> (r : Reachable x) -> (v : Viable n x) ->
>                   (ps : PolicySeq t n) -> M Val
> possibleRewards {t} {n} x r v ps = 
>   fmap (valStateCtrlSeq t n) (possibleStateCtrlSeqs {t} {n} x r v ps)

> |||
> possibleRewards' : {t : Nat} -> {n : Nat} -> M (StateCtrlSeq t n) -> M Val
> possibleRewards' {t} {n} xys = fmap (valStateCtrlSeq t n) xys


