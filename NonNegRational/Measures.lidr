> module NonNegRational.Measures

> import Syntax.PreorderReasoning

> import NonNegRational.NonNegRational
> import NonNegRational.BasicOperations
> import NonNegRational.BasicProperties
> import Nat.Positive
> import Fraction.Fraction
> import Fraction.Normal
 
> %default total
> %access public export
> %auto_implicits off


> ||| 
> factor : {A : Type} -> List A -> NonNegRational
> factor Nil = 1
> factor (a :: as) = fromFraction (1, Element (S (length as)) MkPositive)


> ||| 
> average : List NonNegRational -> NonNegRational
> average xs = (sum xs) * (factor xs)


> {-

> ---}
 
