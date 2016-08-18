> module Sigma.Operations

> -- import Data.Fin
> -- import Data.Vect
> -- import Control.Isomorphism

> import Sigma.Sigma
> -- import Finite.Finite
> -- import Decidable.Decidable
> -- import Finite.Operations
> -- import Vect.Operations


> %default total

> %access public export


> |||
> outl : {A : Type} -> {P : A -> Type} -> Sigma A P -> A
> outl (MkSigma a _) = a


> |||
> outr : {A : Type} -> {P : A -> Type} -> (s : Sigma A P) -> P (outl s)
> outr (MkSigma _ p) = p


> {-

> ||| Maps a finite type |A| and a decidable predicate |P| to a vector |Sigma A P| values
> toVectSigma : {A : Type} ->
>               {P : A -> Type} ->
>               Finite A ->
>               Dec1 P ->
>               Sigma Nat (\ n => Vect n (Sigma A P))
> toVectSigma fA d1P = filterTagSigma d1P (toVect fA)

> ---}
