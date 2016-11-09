> module NonNegRational.tests.Main

> import NonNegRational.NonNegRational
> import NonNegRational.BasicOperations
> import NonNegRational.BasicProperties
> import Fraction.Fraction
> import Fraction.Predicates
> import Fraction.BasicOperations
> import PNat.PNat
> import PNat.Operations
> import PNat.Properties
> import Nat.Positive

> %default total
> %auto_implicits off

> x  : NonNegRational
> x  = fromFraction (2067, Element 616 MkPositive)

> y  : NonNegRational
> y  = fromFraction (32, Element 11 MkPositive)

> z  : NonNegRational
> z  = fromFraction (1, Element 13 MkPositive) -- segfaults with 'Element 12749 MkPositive'

> f1  : Fraction
> f1  = (1, Element 8 MkPositive)
> z1  : NonNegRational
> z1  = fromFraction f1

> f2  : Fraction
> f2  = (3, Element 24 MkPositive)
> z2  : NonNegRational
> z2  = fromFraction f2

> f1Eqf2 : f1 `Eq` f2
> f1Eqf2 = Refl

> z1EQz2 : z1 = z2
> z1EQz2 = fromFractionEqLemma f1 f2 f1Eqf2

> zs : List NonNegRational
> zs = [z1, z2]

> szs : sum zs = z1 + z2
> szs = Refl

> main : IO ()
> main = do putStrLn ("x           = " ++ show x)
>           putStrLn ("y           = " ++ show y)
>           putStrLn ("z           = " ++ show z)
>           putStrLn ("x + y       = " ++ show (x + y))
>           putStrLn ("y + x       = " ++ show (y + x))
>           putStrLn ("x * y       = " ++ show (x * y))
>           putStrLn ("y * x       = " ++ show (y * x))
>           putStrLn ("(x + y) + z = " ++ show ((x + y) + z))
>           putStrLn ("x + (y + z) = " ++ show (x + (y + z)))
>           putStrLn ("(x * y) * z = " ++ show ((x * y) * z))
>           putStrLn ("zs          = " ++ show zs)
>           putStrLn ("sum zs      = " ++ show (sum zs))



