> module NonNegRational.BasicOperations


> import NonNegRational.NonNegRational
> import Fraction.Fraction
> import Fraction.BasicOperations
> import Fraction.BasicProperties
> import Fraction.Normalize
> import Fraction.NormalizeProperties
> import Pairs.Operations
> import Sigma.Sigma

> %default total
> %access public export


> ||| 
> toFraction : NonNegRational -> Fraction
> toFraction = getWitness -- PairsOperations.Subset.getWitness
> -- %freeze toFraction


> ||| 
> fromFraction : Fraction -> NonNegRational
> fromFraction x = Element (normalize x) (normalNormalize x)
> %freeze fromFraction


> ||| The numerator of a non-negative rational
> num : NonNegRational -> Nat
> num = num . toFraction
> -- %freeze num


> ||| The denominator of a non-negative rational
> den : NonNegRational -> Nat
> den = den . toFraction 
> -- %freeze den


> ||| Every natural number is a non-negative rational
> fromNat : (n : Nat) -> NonNegRational
> fromNat = fromFraction . fromNat
> -- %freeze fromNat


> ||| Addition of non-negative rational numbers
> plus : NonNegRational -> NonNegRational -> NonNegRational
> plus x y = fromFraction (toFraction x + toFraction y)
> -- %freeze plus


> ||| Multiplication of non-negative rational numbers
> mult : NonNegRational -> NonNegRational -> NonNegRational
> mult x y = fromFraction (toFraction x * toFraction y)
> -- %freeze mult


