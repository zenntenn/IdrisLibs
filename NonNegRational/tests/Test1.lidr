> module NonNegRational.tests.Main

> import NonNegRational.NonNegRational
> import NonNegRational.BasicOperations
> import NonNegRational.BasicProperties
> import Fraction.Fraction
> import PNat.PNat
> import Nat.Positive

> %default total
> %auto_implicits off

> postulate sumOneLemma : {m, n, d : Nat} -> m + n = S d -> 
>                         fromFraction (m, Element (S d) MkPositive) 
>                         + 
>                         fromFraction (n, Element (S d) MkPositive) 
>                         = 
>                         1

> x  : NonNegRational
> x  = fromFraction (9, Element 10 MkPositive) 

> y  : NonNegRational
> y  = fromFraction (1, Element 10 MkPositive) 

> p : x + y = 1
> p = sumOneLemma Refl
