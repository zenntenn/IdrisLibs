> module Tuple.Properties

> import Control.Isomorphism

> %default total
> %access public export
> %auto_implicits off

> |||
> tuplePairIso3 : {A, B, C : Type} -> Iso (A, B, C) ((A, B), C)
> tuplePairIso3 {A} {B} {C} = MkIso to from ok1 ok2
>   where to : (A, B, C) -> ((A, B), C)
>         to (x, y, z) = ((x, y), z)
>         from : ((A, B), C) -> (A, B, C)
>         from ((x, y), z) = (x, y, z)
>         ok1 : (x : ((A, B), C)) -> to (from x) = x
>         ok1 ((x, y), z) = Refl
>         ok2 : (x : (A, B, C)) -> from (to x) = x
>         ok2 (x, y, z) = Refl  

> |||
> tuplePairIso4 : {A, B, C, D : Type} -> Iso (A, B, C, D) ((A, B, C), D)
> tuplePairIso4 {A} {B} {C} {D} = MkIso to from ok1 ok2
>   where to : (A, B, C, D) -> ((A, B, C), D)
>         to (a, b, c, d) = ((a, b, c), d)
>         from : ((A, B, C), D) -> (A, B, C, D)
>         from ((a, b, c), d) = (a, b, c, d)
>         ok1 : (x : ((A, B, C), D)) -> to (from x) = x
>         ok1 ((a, b, c), d) = Refl
>         ok2 : (x : (A, B, C, D)) -> from (to x) = x
>         ok2 (a, b, c, d) = Refl  
