> module Double.Predicates

> import Data.So

> %default total
> %access public export
> %auto_implicits on


* LT

> |||
> data LT : Double -> Double -> Type where
>   MkLT : {x : Double} -> {y : Double} -> So (x < y) -> LT x y


* LTE

> |||
> data LTE : Double -> Double -> Type where
>   MkLTE : {x : Double} -> {y : Double} -> So (x <= y) -> LTE x y


* Non-negative, positive

> -- |||
> -- data NonNegative : Double -> Type where
> --   MkNonNegative : {x : Double} -> So (0.0 <= x) -> NonNegative x

> -- |||
> -- data Positive : Double -> Type where
> --   MkPositive : {x : Double} -> So (0.0 < x) -> Positive x

> |||
> NonNegative : (x : Double) -> Type
> NonNegative x = 0.0 `LTE` x

> |||
> Positive : (x : Double) -> Type
> Positive x = 0.0 `LT` x



