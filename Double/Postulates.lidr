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



