> module SimpleProb

> import NonNegRational.NonNegRational
> import NonNegRational.BasicProperties
> import Num.Refinements
> import List.Operations

> %default total
> %access public export
> %auto_implicits off


> |||
> data SimpleProb : Type -> Type where
>   MkSimpleProb : {A : Type} ->
>                  (aps : List (A, NonNegRational)) ->
>                  sumMapSnd aps = 1 ->
>                  SimpleProb A


> {-

> ---}
