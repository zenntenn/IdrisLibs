> module NonNegDouble.BasicProperties

> import Double.Predicates
> import NonNegDouble.NonNegDouble
> import NonNegDouble.BasicOperations

> %default total
> %access public export


* Implementations:

> ||| NonNegDouble is an implementation of Show
> implementation Show NonNegDouble where
>   show = show . toDouble 

> ||| NonNegDouble is an implementation of Num
> implementation Num NonNegDouble where
>   (+) = plus
>   (*) = mult
>   fromInteger = fromNat . fromIntegerNat


> {-

> ---}
