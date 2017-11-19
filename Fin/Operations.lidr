> module Fin.Operations

> import Data.Fin
> import Data.Vect


> %default total

> %access public export


> ||| 'Tail' of a finite function
> tail : {A : Type} -> {n : Nat} ->
>        (Fin (S n) -> A) -> (Fin n -> A)
> -- tail f k = f (FS k)
> tail f = f . FS


> ||| Maps a finite function to a vector
> toVect : {A : Type} -> {n : Nat} ->
>          (Fin n -> A) -> Vect n A
> toVect {n =   Z} _ = Nil
> toVect {n = S m} f = (f FZ) :: (toVect (tail f))
> -- toVect f = map f range

> ||| Sum of the values of a finite function
> sum : {n : Nat} -> (Fin n -> Nat) -> Nat
> sum {n = Z}   f = Z
> sum {n = S m} f = f FZ + sum (tail f)


> ||| Fold function for Fin
> foldFin : {X : Nat -> Type} -> (f1 : (n : Nat) -> X (S n)) ->
>                                (f2 : (n : Nat) -> X n -> X (S n)) ->
>                                Fin n -> X n
> foldFin {n = Z} f1 f2 x impossible
> foldFin {n = S m} f1 f2 FZ = f1 m
> foldFin {n = S m} f1 f2 (FS i) = f2 m (foldFin f1 f2 i)

Obs: Previous functions are not folds, since they do not take a |Fin|
as argument.

