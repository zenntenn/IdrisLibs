> module NonNegDouble.Constants

> import Data.So

> import Double.Predicates
> import NonNegDouble.NonNegDouble

> %default total
> %access public export


> ||| 
> zero : NonNegDouble
> zero = Element 0.0 (MkNonNegative Oh)


> ||| 
> one : NonNegDouble
> one = Element 1.0 (MkNonNegative Oh)

