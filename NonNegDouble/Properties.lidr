> import Data.So

> %default total

> data LTE : Double -> Double -> Type where
>   MkLTE : {x : Double} -> {y : Double} -> So (x <= y) -> LTE x y

> NonNegDouble : Type
> NonNegDouble = Subset Double (\ x => 0.0 `LTE` x)

> zero     : NonNegDouble
> one      : NonNegDouble
> toDouble : NonNegDouble -> Double
> plus     : NonNegDouble -> NonNegDouble -> NonNegDouble
> mult     : NonNegDouble -> NonNegDouble -> NonNegDouble
> div      : NonNegDouble -> NonNegDouble -> NonNegDouble
> fromNat  : (n : Nat) -> NonNegDouble

> implementation [NumNonNegDouble] Num NonNegDouble where
>   (+) = plus
>   (*) = mult
>   fromInteger = fromNat . fromIntegerNat

> using implementation NumNonNegDouble
>   ||| NonNegDouble is an implementation of Fractional
>   implementation [FractionalNonNegDouble] Fractional NonNegDouble where
>     (/) = div

> ||| NonNegDouble is an implementation of Eq
> implementation [EqNonNegDouble] Eq NonNegDouble where
>   (==) x y = (toDouble x) == (toDouble y)

> using implementation NumNonNegDouble
>   using implementation EqNonNegDouble
>     ||| NonNegDouble is an implementation of Ord
>     implementation [OrdNonNegDouble] Ord NonNegDouble where
>       compare x y = compare (toDouble x) (toDouble y)
