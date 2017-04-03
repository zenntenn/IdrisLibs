> module NonNegDouble.Measures

> import NonNegDouble.NonNegDouble
> import NonNegDouble.Constants
> import NonNegDouble.Operations
> import NonNegDouble.Properties
 
> %default total
> %access public export
> %auto_implicits off


> ||| 
> average : List NonNegDouble -> NonNegDouble
> average xs = (sum xs) * ( one / fromNat (length xs))

> {-

> ---}
 
