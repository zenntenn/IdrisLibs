> module Double.Properties

> import Data.So

> import Double.Predicates
> import Double.Postulates
> import Double.LTEPostulates
> import So.Properties

> %default total
> %access public export
> %auto_implicits on


> ||| zero is not positive
> notPositiveZero : Not (Positive 0.0)
> notPositiveZero (MkPositive prf) = contra Refl prf

> |||
> positiveImpliesNonNegative : {x : Double} -> Positive x -> NonNegative x
> positiveImpliesNonNegative (MkPositive prf) = MkNonNegative (LTinLTE prf) 
