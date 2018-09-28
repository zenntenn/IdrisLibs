> module Vect.Operations


> import Data.Vect
> import Data.Fin
> import Data.So

> import Decidable.Predicates
> import Rel.TotalPreorder
> import Rel.TotalPreorderOperations
> import Nat.LTProperties
> import Sigma.Sigma


> %default total
> %access public export
> %auto_implicits on


Lookup

> ||| Lookup the index of an element of a vector
> lookup : {A : Type} -> .(a : A) -> .(as : Vect n A) -> Elem a as -> Fin n
> lookup {n = Z}   a  Nil        Here         impossible
> lookup {n = Z}   a  Nil       (There p)     impossible
> lookup {n = S m} a (a :: as)   Here       = FZ
> lookup {n = S m} a (a' :: as) (There prf) = FS (lookup a as prf)

> ||| Lookup the index of an element of a vector
> -- lookup' : {n : Nat} -> {A : Type} -> (DecEq A) => (a : A) -> (as : Vect n A) -> Maybe (Fin n)
> lookup' : {n : Nat} -> {A : Type} -> (DecEq A) -> (a : A) -> (as : Vect n A) -> Maybe (Fin n)
> lookup' {n = Z}   _ _  Nil        = Nothing
> lookup' {n = S m} d a  (a' :: as) with (decEq a a')
>   | (Yes _) = Just FZ
>   | (No  _) with (lookup' d a as)
>     | Nothing  = Nothing
>     | (Just k) = Just (FS k)


Container monad operations

...


Filtering

> ||| Filters a vector on a decidable property
> filter : {A : Type} ->
>          {P : A -> Type} ->
>          Dec1 P ->
>          Vect n A -> 
>          Sigma Nat (\ m => Vect m A)
> filter d1P Nil = MkSigma Z Nil
> filter d1P (a :: as) with (filter d1P as)
>   | (MkSigma n as') with (d1P a)
>     | (Yes _) = MkSigma (S n) (a :: as')
>     | (No  _) = MkSigma n as'


> ||| Filters a vector on a decidable property and pairs elements with proofs
> filterTagSigma : {A : Type} ->
>                  {P : A -> Type} ->
>                  Dec1 P ->
>                  Vect n A -> 
>                  Sigma Nat (\ m => Vect m (Sigma A P))
> filterTagSigma d1P Nil = MkSigma _ Nil
> filterTagSigma d1P (a :: as) with (filterTagSigma d1P as)
>   | (MkSigma _ tail) with (d1P a)
>     | (Yes p) = MkSigma _ ((MkSigma a p) :: tail)
>     | (No  _) = MkSigma _ tail


> ||| Filters a vector on a decidable property and pairs elements with proofs
> filterTagExists : {A : Type} ->
>                   {P : A -> Type} ->
>                   Dec1 P ->
>                   Vect n A -> 
>                   Sigma Nat (\ m => Vect m (Exists {a = A} P))
> filterTagExists d1P Nil = MkSigma _ Nil
> filterTagExists d1P (a :: as) with (filterTagExists d1P as)
>   | (MkSigma _ tail) with (d1P a)
>     | (Yes p) = MkSigma _ ((Evidence a p) :: tail)
>     | (No  _) = MkSigma _ tail


> ||| Filters a vector on a decidable property and pairs elements with proofs
> filterTagSubset : {A : Type} ->
>                   {P : A -> Type} ->
>                   Dec1 P ->
>                   Vect n A -> 
>                   Sigma Nat (\ m => Vect m (Subset A P))
> filterTagSubset d1P Nil = MkSigma _ Nil
> filterTagSubset d1P (a :: as) with (filterTagSubset d1P as)
>   | (MkSigma _ tail) with (d1P a)
>     | (Yes p) = MkSigma _ ((Element a p) :: tail)
>     | (No  _) = MkSigma _ tail

Searching

> |||
> argmaxMax : {A : Type} -> {R : A -> A -> Type} -> 
>             TotalPreorder R -> Vect n A -> .(LT Z n) -> (Fin n, A)
> argmaxMax {n = Z}       tp  Nil                p = absurd p
> argmaxMax {n = S Z}     tp (a :: Nil)          _ = (FZ, a)
> argmaxMax {n = S (S m)} tp (a' :: (a'' :: as)) _ with (argmaxMax tp (a'' :: as) (ltZS m))
>   | (k, max) with (totalPre tp a' max)
>     | (Left  _) = (FS k, max)
>     | (Right _) = (FZ, a')


> |||
> argmax : {A : Type} -> {R : A -> A -> Type} -> 
>          TotalPreorder R -> Vect n A -> .(LT Z n) -> Fin n
> argmax tp as p = fst (argmaxMax tp as p)


> |||
> max : {A : Type} -> {R : A -> A -> Type} -> 
>       TotalPreorder R -> Vect n A -> .(LT Z n) -> A
> max tp as p = snd (argmaxMax tp as p)


> {-

> |||
> argmaxMax : {A : Type} ->
>             TotalPreorder A -> Vect n A -> .(LT Z n) -> (Fin n, A)
> argmaxMax {n = Z}       tp  Nil                p = absurd p
> argmaxMax {n = S Z}     tp (a :: Nil)          _ = (FZ, a)
> argmaxMax {n = S (S m)} tp (a' :: (a'' :: as)) _ with (argmaxMax tp (a'' :: as) (ltZS m))
>   | (k, max) with (totalPre tp a' max)
>     | (Left  _) = (FS k, max)
>     | (Right _) = (FZ, a')


> |||
> argmax : {A : Type} ->
>          TotalPreorder A -> Vect n A -> .(LT Z n) -> Fin n
> argmax tp as p = fst (argmaxMax tp as p)


> |||
> max : {A : Type} ->
>       TotalPreorder A -> Vect n A -> .(LT Z n) -> A
> max tp as p = snd (argmaxMax tp as p)

> -}


Show

> implementation Show (Elem a as) where
>   show = show' where
>     show' : {n : Nat} -> {A : Type} -> {a : A} -> {as : Vect n A} -> Elem a as -> String 
>     show'  Here     = "Here"
>     show' (There p) = "There" ++ show' p


Pointwise modify

> |||
> modifyVect : {n : Nat} -> {a : Type} ->
>              Vect n a -> Fin n -> a -> Vect n a
> modifyVect {n = Z}    Nil          k  _  = absurd k
> modifyVect {n = S m} (a :: as)  FZ    a' = a' :: as
> modifyVect {n = S m} (a :: as) (FS k) a' = a :: (modifyVect as k a')


Fold:

data Vect : Nat -> Type -> Type where
  Nil : Vect Z A
  Cons : A -> Vect n A -> Vect (S n) A

x0 : X 0
f  : A -> X n -> X (S n)


> foldVect : {X : Nat -> Type} -> 
>            {A : Type} ->
>            X 0 ->
>            ((n : Nat) -> A -> X n -> X (S n)) ->
>            Vect n A ->
>            X n
> foldVect {n = Z} x0 f Nil = x0
> foldVect {n = S m} x0 f (a :: as) = f m a (foldVect x0 f as)


> {-

> |||
> argmaxMax : {A : Type} -> {TO : A -> A -> Type} -> Preordered A TO =>
>             Vect (S n) A -> (Fin (S n), A)
> argmaxMax     {n = Z}   (a :: Nil) = (FZ, a)
> argmaxMax {A} {n = S m} (a :: (a' :: as)) with (preorder a (snd (argmaxMax (a' :: as))))
>   | (Left  _) = (FS (fst ka), snd ka) where
>     ka : (Fin (S m), A)
>     ka = argmaxMax (a' :: as)
>   | (Right _) = (FZ, a)


> |||
> argmax : {A : Type} -> {TO : A -> A -> Type} -> Preordered A TO =>
>          Vect (S n) A -> Fin (S n)
> argmax = fst . argmaxMax


> |||
> max : {A : Type} -> {TO : A -> A -> Type} -> Preordered A TO =>
>       Vect (S n) A -> A
> max = snd . argmaxMax

> -}


> {-

> |||
> argmaxMax : {A, F : Type} -> {TO : F -> F -> Type} -> Ordered F TO =>
>             Vect (S n) (A,F) -> (A,F)
> argmaxMax {n = Z}   (af :: Nil) = af
> argmaxMax {n = S m} (af :: (af' :: afs)) with (order (snd af) (snd (argmaxMax (af' :: afs))))
>   | (Left  _) = argmaxMax (af' :: afs)
>   | (Right _) = af


> |||
> argmax : {A, F : Type} -> {TO : F -> F -> Type} -> Ordered F TO =>
>          Vect (S n) (A,F) -> A
> argmax = fst . argmaxMax


> |||
> max : {A, F : Type} -> {TO : F -> F -> Type} -> Ordered F TO =>
>       Vect (S n) (A,F) -> F
> max = snd . argmaxMax

> ---}
 
> ---}

 
