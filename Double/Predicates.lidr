> module Double.Predicates

> import Data.So

> %default total
> %access public export
> %auto_implicits on


> |||
> data NonNegative : Double -> Type where
>   MkNonNegative : {x : Double} -> So (0.0 <= x) -> NonNegative x

> |||
> data Positive : Double -> Type where
>   MkPositive : {x : Double} -> So (0.0 < x) -> Positive x


