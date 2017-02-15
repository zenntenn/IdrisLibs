> module Functor.Properties

> import Functor.Predicates

> %default total
> %access public export
> %auto_implicits off


* Monotonicity and naturality:

> ||| Composing a monotone measure with a natural transformation
> ||| yields a monotone measure
> monotoneNaturalLemma: {B, C : Type} -> {F : Type -> Type} -> (Functor F) => 
>                       (LTE_B : B -> B -> Type) -> 
>                       (LTE_C : C -> C -> Type) -> 
>                       (measure : F B -> C) ->
>                       Monotone LTE_B LTE_C measure -> 
>                       (t : (A : Type) -> F A -> F A) -> 
>                       Natural t -> 
>                       Monotone LTE_B LTE_C (measure . (t B))
>
> monotoneNaturalLemma {B} {C} {F} LTE_B LTE_C m mm t nt = mmt where
>   mmt : Monotone {B} {C} {F} LTE_B LTE_C (m . (t B))
>   mmt A f g p x = s3 where
>     s1 : m (map f (t A x)) `LTE_C` m (map g (t A x))
>     s1 = mm A f g p (t A x)
>     s2 : m ((t B) (map f x)) `LTE_C` m (map g (t A x))
>     s2 = replace {P = \ X => m X `LTE_C` m (map g (t A x))} (sym (nt f x)) s1
>     s3 : m ((t B) (map f x)) `LTE_C` m ((t B) (map g x))
>     s3 = replace {P = \ X => m ((t B) (map f x)) `LTE_C` m X} (sym (nt g x)) s2


> {-


> ---}
