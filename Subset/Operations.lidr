> module Subset.Operations

> import Data.Fin
> import Data.Vect
> import Control.Isomorphism

> import Sigma.Sigma
> import Pairs.Operations
> import Finite.Predicates
> import Decidable.Predicates
> import Finite.Operations
> import Vect.Operations


> %default total

> %access public export


> |||
> outl : {A : Type} -> {P : A -> Type} -> Subset A P -> A
> outl = getWitness


> |||
> outr : {A : Type} -> {P : A -> Type} -> (s : Subset A P) -> P (outl s)
> outr = getProof


> ||| Maps a finite type |A| and a decidable predicate |P| to a vector |Subset A P| values
> toVectSubset : {A : Type} ->
>                {P : A -> Type} ->
>                Finite A ->
>                Dec1 P ->
>                Sigma Nat (\ n => Vect n (Subset A P))
> toVectSubset fA d1P = filterTagSubset d1P (toVect fA)
