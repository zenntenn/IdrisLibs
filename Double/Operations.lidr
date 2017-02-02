> module Double.Operations

> import Data.So
> import Data.Fin

> import Double.Predicates
> import So.Properties

> %default total
> %access public export


> ||| 
> fromNat : (n : Nat) -> Double
> fromNat  Z    = 0.0
> fromNat (S m) = 1.0 + (fromNat m)

> ||| 
> fromFin : {n : Nat} -> Fin n -> Double
> fromFin = fromNat . finToNat

> |||
> mkLinear : Double -> Double -> Double -> Double
> mkLinear a b x = a + b * x

> mkLinearStep : (x1 : Double) -> (x2 : Double) -> Positive (x2 - x1) -> 
>                (y1 : Double) -> (y2 : Double) -> 
>                Double -> Double
> mkLinearStep x1 x2 px2mx1 y1 y2 x with (decSo (x < x1))
>   | Yes _ = y1
>   | No  _ with (decSo (x1 <= x && x <= x2))
>     | Yes _ = y1 * (1.0 - alpha) + y2 * alpha where
>         alpha : Double
>         alpha = (x - x1) / (x2 - x1)
>     | No  _ = y2

