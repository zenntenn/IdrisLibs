> module NonNegDouble.BasicOperations

> import Data.So

> import Double.Predicates
> import Double.Postulates
> import NonNegDouble.NonNegDouble
> import Pairs.Operations

> %default total
> %access public export


> ||| 
> toDouble : NonNegDouble -> Double
> toDouble = getWitness -- PairsOperations.Subset.getWitness


> ||| 
> fromDouble : (x : Double) -> NonNegative x -> NonNegDouble
> fromDouble x prf = Element x prf


> ||| Addition of positive double precision floating point numbers
> plus : NonNegDouble -> NonNegDouble -> NonNegDouble
> plus (Element x px) (Element y py) = Element (x + y) (plusPreservesNonNegativity px py)


> ||| Multiplication of positive double precision floating point numbers
> mult : NonNegDouble -> NonNegDouble -> NonNegDouble
> mult (Element x px) (Element y py) = Element (x * y) (multPreservesNonNegativity px py)


> ||| 
> fromNat : (n : Nat) -> NonNegDouble
> fromNat  Z    = Element 0.0 (MkNonNegative Oh) 
> fromNat (S m) = plus (Element 1.0 (MkNonNegative Oh)) (fromNat m)
