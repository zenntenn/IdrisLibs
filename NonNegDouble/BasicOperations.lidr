> module NonNegDouble.BasicOperations

> import Data.So

> import Double.Predicates
> import Double.Postulates
> import Double.Properties
> import NonNegDouble.NonNegDouble
> import NonNegDouble.Constants
> import Pairs.Operations

> %default total
> %access public export


> ||| 
> mkNonNegDouble : (x : Double) -> {auto prf : 0.0 `LTE` x} -> NonNegDouble 
> mkNonNegDouble x {prf} = Element x prf


> ||| 
> cast : (x : Double) -> {auto prf : 0.0 `LTE` x} -> NonNegDouble 
> cast = mkNonNegDouble


> ||| 
> toDouble : NonNegDouble -> Double
> toDouble = getWitness


> ||| 
> fromDouble : (x : Double) -> NonNegative x -> NonNegDouble
> fromDouble x prf = Element x prf


> {-


> ---}
