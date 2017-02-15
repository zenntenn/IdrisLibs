> module Functor.Predicates

> %default total
> %access public export
> %auto_implicits off


* Naturality

> ||| What it means for a transformation to be natural
> Natural : {F, G : Type -> Type} -> 
>           (Functor F) => (Functor G) =>
>           (t : {A : Type} -> F A -> G A) -> 
>           Type            
>            
> Natural {F} {G} t = {A, B : Type} -> 
>                     (f : A -> B) ->
>                     (x : F A) -> 
>                     t (map f x) = map f  (t x) 

> {-
> ||| What it means for a transformation to be natural
> Natural : {F, G : Type -> Type} -> 
>           (Functor F) => (Functor G) =>
>           (t : (A : Type) -> F A -> G A) -> 
>           Type            
>            
> Natural {F} {G} t = {A, B : Type} -> 
>                     (f : A -> B) ->
>                     (x : F A) -> 
>                     t B (map f x) = map f (t A x) 
> -}


* Monotonicity

> ||| What it means for a measure to be monotone
> Monotone : {B, C : Type} -> {F : Type -> Type} -> (Functor F) => 
>            (LTE_B : B -> B -> Type) -> 
>            (LTE_C : C -> C -> Type) -> 
>            (measure : F B -> C) -> 
>            Type
>            
> Monotone {B} {C} {F} LTE_B LTE_C measure =
>   {A : Type} ->
>   (f : A -> B) -> 
>   (g : A -> B) -> 
>   (p : (a : A) -> f a `LTE_B` g a) -> 
>   (x : F A) -> 
>   measure (map f x) `LTE_C` measure (map g x)  


> {-


> ---}
