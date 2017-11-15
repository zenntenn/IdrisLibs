> import Data.So

> %default total

> data LTE : Double -> Double -> Type where
>   MkLTE : {x : Double} -> {y : Double} -> So (x <= y) -> LTE x y

> NonNegDouble : Type
> NonNegDouble = Subset Double (\ x => 0.0 `LTE` x)

> zero     : NonNegDouble
> one      : NonNegDouble
> toDouble : NonNegDouble -> Double
> toDouble = getWitness
> plus     : NonNegDouble -> NonNegDouble -> NonNegDouble
> mult     : NonNegDouble -> NonNegDouble -> NonNegDouble
> div      : NonNegDouble -> NonNegDouble -> NonNegDouble
> fromNat  : (n : Nat) -> NonNegDouble

> implementation [NumNonNegDouble] Num NonNegDouble where
>   (+) = plus
>   (*) = mult
>   fromInteger = fromNat . fromIntegerNat

> using implementation NumNonNegDouble
>   implementation [FractionalNonNegDouble] Fractional NonNegDouble where
>     (/) = div

> implementation [EqNonNegDouble] Eq NonNegDouble where
>   (==) x y = (toDouble x) == (toDouble y)

> using implementation EqNonNegDouble
>   %assert_total 
>   implementation [OrdNonNegDouble] Ord NonNegDouble where
>     compare x y = compare (toDouble x) (toDouble y)
