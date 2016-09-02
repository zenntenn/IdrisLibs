> module Rel.Preorder


> %default total
> %access public export


> ||| Preorder
> data Preorder : Type -> Type where
>   MkPreorder : {A : Type} ->
>                (R : A -> A -> Type) ->
>                (reflexive : (x : A) -> R x x) ->
>                (transitive : (x : A) -> (y : A) -> (z : A) -> R x y -> R y z -> R x z) ->
>                Preorder A


