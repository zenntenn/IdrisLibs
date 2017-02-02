> module Functor.Predicates

> %default total
> %access public export
> %hide elem

* Monotonicity

> |||
> Monotone : {A, B, C : Type} -> {F : Type -> Type} -> (Functor F) => 
>            (LTE_B : B -> B -> Type) -> 
>            (LTE_C : C -> C -> Type) -> 
>            (measure : F B -> C) -> 
>            Type
>            
> Monotone {A} {B} {C} {F} LTE_B LTE_C measure = 
>   (f : A -> B) -> 
>   (g : A -> B) -> 
>   (p : (a : A) -> f a `LTE_B` g a) -> 
>   (x : F A) -> 
>   measure (map f x) `LTE_C` measure (map g x)  


