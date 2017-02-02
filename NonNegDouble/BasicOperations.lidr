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
> toDouble : NonNegDouble -> Double
> toDouble = getWitness


> ||| 
> fromDouble : (x : Double) -> NonNegative x -> NonNegDouble
> fromDouble x prf = Element x prf


> ||| Addition of positive double precision floating point numbers
> plus : NonNegDouble -> NonNegDouble -> NonNegDouble
> plus (Element x nnx) (Element y nny) = Element (x + y) (plusPreservesNonNegativity nnx nny)


> ||| Multiplication of positive double precision floating point numbers
> mult : NonNegDouble -> NonNegDouble -> NonNegDouble
> mult (Element x nnx) (Element y nny) = Element (x * y) (multPreservesNonNegativity nnx nny)


> ||| Division of positive double precision floating point numbers
> div : NonNegDouble -> NonNegDouble -> NonNegDouble
> div (Element x nnx) (Element y nny) = Element (x / y) (divPreservesNonNegativity nnx nny)


> ||| 
> fromNat : (n : Nat) -> NonNegDouble
> fromNat  Z    = zero
> fromNat (S m) = one `plus` (fromNat m)


> {-


> ---}
