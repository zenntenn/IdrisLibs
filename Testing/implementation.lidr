> import Data.Vect

> import Enumerated.Enumerated

> %default total
> %auto_implicits off
> %access public export

> data Foo = Zero | One
> 
> implementation Enumerated Foo 2 where
>   values = [Zero, One]
>   toFin Zero = 0
>   toFin  One = 1
>   values_match_toFin = Refl
>   
> implementation Eq Foo where
>   x  == y  = toFin x == toFin y
