> module Double.Postulates

> import Data.So

> import Double.Predicates
> import So.Properties

> %default total
> %access public export
> %auto_implicits on


> |||
> postulate 
> plusPreservesNonNegativity : {x, y : Double} -> 
>                              NonNegative x -> NonNegative y -> NonNegative (x + y) 


> |||
> postulate 
> multPreservesNonNegativity : {x, y : Double} -> 
>                              NonNegative x -> NonNegative y -> NonNegative (x * y)


> |||
> postulate 
> divPreservesNonNegativity : {x, y : Double} -> 
>                             NonNegative x -> NonNegative y -> NonNegative (x / y)


> |||
> postulate 
> positivePlusAnyPositive : {x, y : Double} -> 
>                           Positive x -> NonNegative y -> Positive (x + y)


> |||
> postulate 
> divPreservesPositivity : {x, y : Double} -> 
>                          Positive x -> Positive y -> Positive (x / y)


* Postulates on Ord methods

> |||
> postulate 
> gtLT : {x, y : Double} -> So (x > y) -> So (y < x)

> postulate 
> notCompareEQ : {x, y : Double} -> Not (So (x == y)) -> Not (EQ = compare x y)


