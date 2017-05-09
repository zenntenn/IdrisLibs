> module NonNegDouble.Operations

> import Data.So

> import Double.Predicates
> import Double.Postulates
> import Double.Properties
> import NonNegDouble.NonNegDouble
> import NonNegDouble.Predicates
> import NonNegDouble.Constants
> import NonNegDouble.BasicOperations
> import Pairs.Operations

> %default total
> %access public export


> ||| Addition of positive double precision floating point numbers
> plus : NonNegDouble -> NonNegDouble -> NonNegDouble
> plus (Element x nnx) (Element y nny) = Element (x + y) (plusPreservesNonNegativity nnx nny)

> ||| Subtraction of positive double precision floating point numbers
> minus : (x : NonNegDouble) -> (y : NonNegDouble) -> {auto prf : y `LTE` x} -> NonNegDouble
> minus (Element x nnx) (Element y nny) {prf} = Element (x - y) (minusPreservesNonNegativity nnx nny prf)

> (-) : (x : NonNegDouble) -> (y : NonNegDouble) -> {auto prf : y `LTE` x} -> NonNegDouble
> (-) = minus

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
