> module SequentialDecisionProblems.Utils

> import Data.Fin
> import Control.Isomorphism

> import SequentialDecisionProblems.CoreTheory
> import Finite.Predicates
> import Finite.Operations
> import Finite.Properties
> import Sigma.Sigma
> import Sigma.Operations
> import Sigma.Properties
> import Fun.Operations
> import Decidable.Predicates
> import Decidable.Properties

> %default total
> %access public export
> %auto_implicits off

* Finiteness notions

> |||
> FiniteViable : Type
> FiniteViable = {t : Nat} -> 
>                (n : Nat) -> (x : State t) -> Finite (Viable {t} n x)

> |||
> FiniteAll : Type
> FiniteAll = {A : Type} -> {P : A -> Type} -> 
>             Finite1 P -> (ma : M A) -> Finite (All P ma)

> |||
> FiniteAllViable : Type
> FiniteAllViable = {t : Nat} -> {n : Nat} -> 
>                   (x : State t) -> (y : Ctrl t x) -> 
>                   Finite (All (Viable {t = S t} n) (nexts t x y))

> |||
> FiniteNotEmpty : Type
> FiniteNotEmpty = {t : Nat} -> {n : Nat} -> 
>                  (x : State t) -> (y : Ctrl t x) -> 
>                  Finite (NotEmpty (nexts t x y))

> |||
> FiniteGood : Type
> FiniteGood = {t : Nat} -> {n : Nat} -> 
>              (x : State t) -> (y : Ctrl t x) -> 
>              Finite (Good t x n y)

> |||
> FiniteCtrl : Type
> FiniteCtrl = {t : Nat} -> {n : Nat} -> 
>              (x : State t) -> Finite (Ctrl t x) 

> |||
> FiniteGoodCtrl : Type
> FiniteGoodCtrl = {t : Nat} -> {n : Nat} -> 
>                  (x : State t) -> Viable {t = t} (S n) x ->
>                  Finite (GoodCtrl t x n) 


* Decidability notions

> |||
> DecidableViable : Type
> DecidableViable = {t : Nat} -> 
>                   (n : Nat) -> (x : State t) -> Dec (Viable {t} n x)

> |||
> DecidableAll : Type
> DecidableAll = {A : Type} -> {P : A -> Type} -> 
>                Dec1 P -> (ma : M A) -> Dec (All P ma)

> |||
> DecidableAllViable : Type
> DecidableAllViable = {t : Nat} -> {n : Nat} -> 
>                      (x : State t) -> (y : Ctrl t x) -> 
>                      Dec (All (Viable {t = S t} n) (nexts t x y))

> |||
> DecidableNotEmpty : Type
> DecidableNotEmpty = {t : Nat} -> {n : Nat} -> 
>                     (x : State t) -> (y : Ctrl t x) -> 
>                     Dec (NotEmpty (nexts t x y))

> |||
> DecidableGood : Type
> DecidableGood = {t : Nat} -> {n : Nat} -> 
>                 (x : State t) -> (y : Ctrl t x) -> 
>                 Dec (Good t x n y)

> |||
> DecidableGoodCtrl : Type
> DecidableGoodCtrl = {t : Nat} -> {n : Nat} -> 
>                     (x : State t) -> Viable {t = t} (S n) x ->
>                     Dec (GoodCtrl t x n) 


* Standard deduction patterns in the implementation of specific SDPs

We would like to provide users with a function

< finiteAllViable : FiniteAll -> FiniteViable -> FiniteAllViable

but, as it turns out, implementing this function is not trivial (see
issues 3135 and 3136). Thus, for the time being, we introduce 2
additional assumptions in the global context

> ||| If users can prove that All is finite ... 
> finiteAll : {A : Type} -> {P : A -> Type} -> 
>             Finite1 P -> (ma : M A) -> Finite (All P ma)

> ||| ... and that Viable is finite,
> finiteViable : {t : Nat} -> {n : Nat} -> 
>                (x : State t) -> Finite (Viable {t} n x)

and apply them to deduce finiteness of |All Viable|.

> ||| we can deduce that All Viable is finite
> finiteAllViable : {t : Nat} -> {n : Nat} -> 
>                   (x : State t) -> (y : Ctrl t x) -> 
>                   Finite (All (Viable {t = S t} n) (nexts t x y))
> finiteAllViable {t} {n} x y = finiteAll (finiteViable {t = S t} {n}) (nexts t x y)

Similarly, if users are able to prove that |NotEmpty| is finite

> finiteNotEmpty : {t : Nat} -> {n : Nat} -> 
>                  (x : State t) -> (y : Ctrl t x) -> 
>                  Finite (NotEmpty (nexts t x y))

Finiteness of |NotEmpty| and |All Viable| directly implies finiteness of
|Good|

> |||
> finiteGood : {t : Nat} -> {n : Nat} -> 
>              (x : State t) -> (y : Ctrl t x) -> 
>              Finite (Good t x n y)
> finiteGood {n} x y = finiteProduct (finiteNotEmpty {n} x y) (finiteAllViable x y)

and, assuming finiteness of controls, finiteness of |GoodCtrl|:

> |||
> finiteCtrl : {t : Nat} -> {n : Nat} -> (x : State t) -> Finite (Ctrl t x) 

> ||| 
> finiteGoodCtrl : {t : Nat} -> {n : Nat} -> 
>                  (x : State t) -> 
>                  Finite (GoodCtrl t x n) 
> finiteGoodCtrl {t} {n} x = finiteSigmaLemma0 (finiteCtrl {t} {n} x) (finiteGood {t} {n} x)

Finally, we can show

> |||
> cardNotZGoodCtrl : {t : Nat} -> {n : Nat} -> 
>                    (x : State t) -> (v : Viable {t = t} (S n) x) ->
>                    CardNotZ (finiteGoodCtrl {t} {n} x)
> cardNotZGoodCtrl x v = cardNotZLemma (finiteGoodCtrl x) (viableSpec1 x v)


Similarly, we can provide standard deduction patterns for decidability

> ||| If users can prove that All is decidable ... 
> decidableAll : {A : Type} -> {P : A -> Type} -> 
>                ((a : A) -> Dec (P a)) -> (ma : M A) -> Dec (All P ma)
 
> ||| ... and that Viable is decidable,
> decidableViable : {t : Nat} -> {n : Nat} -> 
>                   (x : State t) -> Dec (Viable {t} n x)

we can deduce decidability of |All Viable|.

> ||| we can deduce that All Viable is decidable
> decidableAllViable : {t : Nat} -> {n : Nat} -> 
>                      (x : State t) -> (y : Ctrl t x) -> 
>                      Dec (All (Viable {t = S t} n) (nexts t x y))
> decidableAllViable {t} {n} x y = decidableAll (decidableViable {t = S t} {n}) (nexts t x y)

Further, if users are able to prove that |NotEmpty| is decidable

> |||
> decidableNotEmpty : {t : Nat} -> {n : Nat} -> 
>                     (x : State t) -> 
>                     (y : Ctrl t x) -> Dec (NotEmpty (nexts t x y))

we can deduce decidability of |Good|

> ||| 
> decidableGood : {t : Nat} -> {n : Nat} -> 
>                 (x : State t) -> 
>                 (y : Ctrl t x) -> Dec (Good t x n y) 
> decidableGood {t} {n} x y = decPair (decidableNotEmpty {t} {n} x y) (decidableAllViable {t} {n} x y)

and, assuming finiteness of controls, decidability of |GoodCtrl|:

> ||| 
> decidableGoodCtrl : {t : Nat} -> {n : Nat} -> 
>                     (x : State t) -> 
>                     Dec (GoodCtrl t x n) 
> decidableGoodCtrl {t} {n} x = finiteDecSigmaLemma (finiteCtrl {t} {n} x) (decidableGood {t} {n} x)


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
> morePossibleStateCtrlSeqs  :  {t, n : Nat} -> (mx : M (State t)) -> 
>                               All Reachable mx -> All (Viable n) mx ->
>                               (ps : PolicySeq t n) -> M (StateCtrlSeq t n)
> morePossibleStateCtrlSeqs {t} {n}  mx ar av ps  =  bind (tagElem mx) f where
>   f : Sigma (State t) (\ x => x `Elem` mx) -> M (StateCtrlSeq t n)
>   f (MkSigma x xemx) = possibleStateCtrlSeqs x r v ps where
>       r  :  Reachable x
>       r  =  allElemSpec0 x mx ar xemx
>       v  :  Viable n x
>       v  =  allElemSpec0 x mx av xemx

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


