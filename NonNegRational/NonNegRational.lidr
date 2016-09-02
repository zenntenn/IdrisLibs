> module NonNegRational.NonNegRational


> import Fraction.Fraction
> import Fraction.Normal


> %default total

> %access public export


> ||| Non negative rational numbers
> NonNegRational : Type
> NonNegRational = Subset Fraction Normal

