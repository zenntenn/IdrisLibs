> module NonNegDouble.open_issues.Main

> import Data.So

> %default total
> %access public export

> data NonNegative : Double -> Type where
>   MkNonNegative : {x : Double} -> So (0.0 <= x) -> NonNegative x

> NonNegDouble : Type
> NonNegDouble = Subset Double NonNegative

> plus : NonNegDouble -> NonNegDouble -> NonNegDouble
> mult : NonNegDouble -> NonNegDouble -> NonNegDouble
> fromNat : Nat -> NonNegDouble

> implementation Num NonNegDouble where
>   (+) = plus
>   (*) = mult
>   fromInteger = fromNat . fromIntegerNat
