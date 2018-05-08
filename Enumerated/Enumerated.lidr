> module Enumerated.Enumerated

> import Data.Vect

> %default total
> %auto_implicits off
> %access public export


> interface Enumerated (t : Type) (len : Nat) | t where
>   values : Vect len t
>   toFin  : t -> Fin len
>   values_match_toFin : map toFin values = range

> {-

> using (t : Type, len : Nat)
>   implementation Enumerated t len => Eq t where
>     x == y = toFin x == toFin y

> -}
