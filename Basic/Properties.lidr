> module Basic.Properties

> import Basic.Operations

> %default total

> %access public export


* Replace properties:


> |||
> replaceLemma : {a : _} -> {x : _} -> {y : _} -> {P : a -> Type} ->
>                (prf : x = y) -> (px : P x) -> replace prf px = px
> replaceLemma Refl px = Refl


> |||
> replaceLemma2 : {A : Type} -> {P : A -> Type} -> {Q : (a : A) -> P a -> Type} ->
>                 {a1 : A} -> {a2 : A} ->
>                 (f : (a : A) -> (pa : P a) -> Q a pa) ->
>                 (prf : a1 = a2) ->
>                 (pa2 : P a2) ->
>                 f a1 (replace (sym prf) pa2) = f a2 pa2
> replaceLemma2 f Refl pa2 = Refl


