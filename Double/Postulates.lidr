> module Double.Postulates

> import Data.So

> import Double.Predicates

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


> |||
> postulate 
> LTinLTE : {x, y : Double} -> So (x < y) -> So (x <= y)


> |||
> postulate 
> EQinLTE : {x, y : Double} -> So (x == y) -> So (x <= y)


> |||
> postulate 
> gtLT : {x, y : Double} -> So (x > y) -> So (y < x)


> |||
> postulate 
> compareLT : {x, y : Double} -> LT = compare x y -> So (x < y)


> |||
> postulate 
> compareEQ : {x, y : Double} -> EQ = compare x y -> So (x == y)


> |||
> postulate 
> compareGT : {x, y : Double} -> GT = compare x y -> So (x > y)
