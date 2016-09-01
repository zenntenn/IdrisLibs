> module GenericSimpleProb.SimpleProb

> import List.Operations

> %default total
> %access public export
> %auto_implicits off


> |||
> data SimpleProb : Type -> Type -> Type where
>   MkSimpleProb : {A, B : Type} ->
>                  Num B =>
>                  (aps : List (A, B)) ->
>                  sumMapSnd aps = 1 ->
>                  SimpleProb A B


> {-

> ---}
