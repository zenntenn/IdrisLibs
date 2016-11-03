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

> n1 : Nat
> n1 = 1

> n2 : Nat
> n2 = 3

> d  : Nat
> d  = 3

> x  : NonNegRational
> x  = fromFraction (n1, Element (S d) MkPositive) 

> y  : NonNegRational
> y  = fromFraction (n2, Element (S d) MkPositive) 

> postulate h : n1 + n2 = S d

> p : x + y = 1
> p = NonNegRational.tests.Main.sumOneLemma {m = n1} {n = n2} {d = d} h
