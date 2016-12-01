> module Functor.Operations

> %default total
> %access public export
> %hide elem

Cezar's membership test:

> |||
> elem : {A : Type} -> {F : Type -> Type} -> 
>        (Functor F) => Eq A => Eq (F Bool) => 
>        A -> F A -> Bool
> elem a fa = map (const True) fa /= map (a /=) fa   


> |||
> Elem : {A : Type} -> {F : Type -> Type} -> 
>        (Functor F) => Eq A => Eq (F Bool) => 
>        A -> F A -> Type
> Elem a fa with (elem a fa)
>   | True  = Unit
>   | False = Void

> |||
> decElem : {A : Type} -> {F : Type -> Type} -> 
>           (Functor F) => Eq A => Eq (F Bool) => 
>           (a : A) -> (fa : F A) -> Dec (a `Elem` fa)
> decElem a fa with (elem a fa)
>   | True  = Yes ()
>   | False = No  id
