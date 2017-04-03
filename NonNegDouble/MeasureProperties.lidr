> module NonNegDouble.MeasureProperties

> import Syntax.PreorderReasoning

> import NonNegDouble.NonNegDouble
> import NonNegDouble.Constants
> import NonNegDouble.Measures
> import NonNegDouble.Operations
> import NonNegDouble.Properties
> import NonNegDouble.Predicates
> import NonNegDouble.LTEProperties
> import List.Properties
 
> %default total
> %access public export
> %auto_implicits off


* Properties of |average|:

> %freeze monotoneSum

> ||| |average| is monotone
> monotoneAverage : {A : Type} ->
>                   (f : A -> NonNegDouble) -> (g : A -> NonNegDouble) ->
>                   (p : (a : A) -> f a `LTE` g a) ->
>                   (as : List A) ->
>                   average (map f as) `LTE` average (map g as) 
> monotoneAverage f g p as = monotoneMultLTE {a = sum (map f as)} 
>                                            {b = sum (map g as)} 
>                                            {c = one / fromNat (length (map f as))} 
>                                            {d = one / fromNat (length (map g as))}
>                                            s1 s3 where
>   s1 : sum (map f as) `LTE` sum (map g as)
>   s1 = monotoneSum f g p as
>   s2 : one / fromNat (length (map f as)) `LTE` one / fromNat (length (map f as))
>   s2 = reflexiveLTE (one / fromNat (length (map f as)))
>   s3 : one / fromNat (length (map f as)) `LTE` one / fromNat (length (map g as))
>   s3 = replace {P = \ X => one / fromNat (length (map f as)) `LTE` one / fromNat X} (lengthLemma as f g) s2


> {-

> ---}
 
