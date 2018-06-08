> module Real.Properties

> import Real.Postulates

> %default total
> %access public export


* Implementations:

> ||| Real is an implementation of Num
> implementation [NumReal] Num Real where
>   (+) = plus
>   (*) = mult
>   fromInteger = fromNat . fromIntegerNat


> using implementation NumReal
>   ||| Real is an implementation of Neg
>   implementation [NegReal] Neg Real where
>     negate x = zero `minus` x
>     (-) = minus


> using implementation NumReal
>   ||| Real is an implementation of Fractional
>   implementation [FractionalReal] Fractional Real where
>     (/) = div


> using implementation NegReal
>   |||
>   minusLemma : {x : Real} -> x - x = 0


> {-

> ---}





