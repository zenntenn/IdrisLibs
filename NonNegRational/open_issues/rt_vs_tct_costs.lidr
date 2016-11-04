> module NonNegRational.open_issues.Main

> import NonNegRational.NonNegRational
> import NonNegRational.BasicOperations
> import NonNegRational.BasicProperties
> import Fraction.Fraction
> import PNat.PNat
> import Nat.Positive

> %default total
> %auto_implicits off

> n : Nat
> n = 1

> x : NonNegRational
> x = fromFraction (1, Element (S n) MkPositive)

> y : NonNegRational
> y = fromFraction (n, Element (S n) MkPositive)

> q : x + y = 1
> q = Refl

> main : IO ()
> main = do putStrLn ("x           = " ++ show x)
>           putStrLn ("y           = " ++ show y)
>           putStrLn ("x + y       = " ++ show (x + y))

For small |n|, type checking time is roughly constant in |n| and
execution time is roughly linear in |n| as one would expect. But:

1) For |n > 399| the computation segfaults

2) Uncommenting lines 22-23 (the computation of |q|) yields unacceptable
   type checking times even for very small |n|:

     n = 1  ->   16 sec.
     n = 2  ->   18 sec.
     n = 3  ->   20 sec.
     n = 4  ->   28 sec.
     n = 5  ->   47 sec.
     n = 6  ->   88 sec.
     n = 7  ->  188 sec.
     n = 8  ->  647 sec.
     n = 9  ->  killed



