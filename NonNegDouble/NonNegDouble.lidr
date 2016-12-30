> module NonNegDouble.NonNegDouble


> import Double.Predicates


> %default total
> %access public export


> ||| Non negative double precision floating point numbers as sigma types
> NonNegDouble : Type
> NonNegDouble = Subset Double NonNegative
