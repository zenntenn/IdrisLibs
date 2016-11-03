> module NonNegRational.pathologies.Main

> import NonNegRational.NonNegRational
> import NonNegRational.BasicOperations
> import NonNegRational.BasicProperties
> import Fraction.Fraction
> import PNat.PNat
> import Nat.Positive

> %default total
> %auto_implicits off

> n : Nat
> n = 5

> x : NonNegRational
> x = fromFraction (1, Element (S n) MkPositive)

> y : NonNegRational
> y = fromFraction (n, Element (S n) MkPositive)

> -- q : x + y = fromFraction (1, Element 1 MkPositive)
> -- q = Refl

> main : IO ()
> main = do putStrLn ("x           = " ++ show x)
>           putStrLn ("y           = " ++ show y)
>           putStrLn ("x + y       = " ++ show (x + y))




