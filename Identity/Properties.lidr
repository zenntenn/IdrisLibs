> module Identity.Properties


> import Control.Monad.Identity

> import Identity.Operations
> import Sigma.Sigma
> import Decidable.Predicates
> import Unique.Predicates
> import Finite.Predicates
> import Unit.Properties


> %default total

> %access public export


> ||| Id is injective
> injectiveId : {a : Type} -> {left : a} -> {right : a} -> (Id left) = (Id right) -> left = right
> injectiveId Refl = Refl
> %freeze injectiveId -- frozen


* |Identity| is a functor:

> -- functorSpec1 : fmap . id = id

> -- functorSpec2 : fmap (f . g) = (fmap f) . (fmap g)


* |Identity| is a monad:

> -- monadSpec1 : (fmap f) . ret = ret . f

> -- monadSpec21 : bind (ret a) f = f a

> -- monadSpec22 : bind ma ret = ma

> -- monadSpec23 : {A, B, C : Type} -> {f : A -> M B} -> {g : B -> M C} ->
> --                bind (bind ma f) g = bind ma (\ a => bind (f a) g)


* |Identity| is a container monad:

> |||
> elemNonEmptySpec0 : {A : Type} ->
>                     (a : A) -> (ia : Identity A) ->
>                     a `Elem` ia -> NonEmpty ia
> elemNonEmptySpec0 a (Id a) Refl = ()   

> ||| 
> elemNonEmptySpec1 : {A : Type} ->
>                     (ia : Identity A) ->
>                     NonEmpty ia -> 
>                     Sigma A (\ a => a `Elem` ia)
> elemNonEmptySpec1 (Id a) _ = (MkSigma a Refl)

> |||
> containerMonadSpec1 : {A : Type} -> {a : A} -> a `Elem` (ret a)
> containerMonadSpec1 {A} {a} = Refl

> -- containerMonadSpec2 : {A : Type} -> (a : A) -> (ma : M A) -> (mma : M (M A)) ->
> --                       a `Elem` ma -> ma `Elem` mma -> a `Elem` (join mma)

> -- containerMonadSpec2 : {A : Type} -> (a : A) -> (ma : M A) -> (mma : M (M A)) ->
> --                       a `Elem` ma -> ma `Elem` mma -> a `Elem` (join mma)

> containerMonadSpec3 : {A : Type} -> {P : A -> Type} -> 
>                       (a : A) -> (ia : Identity A) -> All P ia -> a `Elem` ia -> P a
> containerMonadSpec3 {A} {P} a1 (Id a2) pa2 a1eqa2 = replace (sym a1eqa2) pa2

> -- containerMonadSpec4 : {A : Type} -> (ia : Identity A) -> fmap outl (tagElem ia) = ia

> -- containerMonadSpec5 : {A : Type} -> {P : A -> Type} -> 
> --                       (ia : Identity A) -> ((a : A) -> a `Elem` ia -> P a) -> All P ia 


* Specific container monad properties

> |||
> -- uniqueAllLemma : {A : Type} -> {P : A -> Type} -> 
> --                  Unique1 P -> (ia : Identity A) -> Unique (All P ia)

> ||| All is finite
> finiteAll : {A : Type} -> {P : A -> Type} ->
>             Finite1 P -> (ia : Identity A) -> Finite (All P ia)
> finiteAll f1P (Id a) = f1P a

> ||| All is decidable
> decidableAll : {A : Type} -> {P : A -> Type} -> 
>                (dec : (a : A) -> Dec (P a)) -> (ia : Identity A) -> Dec (All P ia)
> decidableAll dec ia = dec (unwrap ia)

> ||| NotEmpty is finite
> finiteNonEmpty : {A : Type} -> (ia : Identity A) -> Finite (NonEmpty ia)
> finiteNonEmpty _ = finiteUnit

> ||| NonEmpty is decidable
> decidableNonEmpty : {A : Type} -> (ia : Identity A) -> Dec (NonEmpty ia)
> decidableNonEmpty _ = Yes ()


> ||| Values of type |Identity A| are never empty
> nonEmptyLemma : {A : Type} -> (ia : Identity A) -> NonEmpty ia
> nonEmptyLemma (Id a) = elemNonEmptySpec0 a (Id a) Refl                

> ||| |Elem| is decidable
> decElem : {A : Type} -> DecEq0 A -> (a : A) -> (ma : Identity A) -> Dec (a `Elem` ma)
> decElem dec a1 (Id a2) with (dec a1 a2)
>   | (Yes prf)   = Yes prf
>   | (No contra) = No contra
> %freeze decElem -- frozen

> ||| |Elem| is unique
> uniqueElem : {A : Type} -> UniqueEq0 A -> (a : A) -> (ma : Identity A) -> Unique (a `Elem` ma)
> uniqueElem unique a1 (Id a2) p q = unique a1 a2 p q
> %freeze uniqueElem -- frozen


Eq

> using (A : Type)
>   implementation (Eq A) => Eq (Identity A) where
>     (Id a) == (Id b) = a == b


Show

> using (A : Type)
>   implementation (Show A) => Show (Identity A) where
>     show (Id a) = show a


> {-

> ---}
