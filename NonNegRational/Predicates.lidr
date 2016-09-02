> module NonNegRational.Predicates

> import NonNegRational.NonNegRational
> import NonNegRational.BasicOperations
> import Fraction.Fraction
> import Fraction.Predicates

> %default total
> %access public export
> %auto_implicits off


> ||| Proofs that `x` is less than or equal to `y`                                                                          
> ||| @ x the smaller number                                                                                                
> ||| @ y the larger number
> LTE : (x, y : NonNegRational) -> Type
> LTE x y = Fraction.Predicates.LTE (toFraction x) (toFraction y)





