> module Double.Properties

> import Data.So

> import Double.Predicates
> import Double.Postulates
> import Double.LTEPostulates
> import So.Properties
> import Ordering.Properties

> %default total
> %access public export
> %auto_implicits on


> ||| zero is not positive
> notPositiveZero : Not (Positive 0.0)
> notPositiveZero (MkPositive prf) = contra Refl prf


* Properties of Ord methods

> |||
> LTinLTE : {x, y : Double} -> So (x < y) -> So (x <= y)
> LTinLTE {x} {y} prf = soOrIntro1 (x < y) (x == y) prf

> |||
> EQinLTE : {x, y : Double} -> So (x == y) -> So (x <= y)
> EQinLTE {x} {y} prf = soOrIntro2 (x < y) (x == y) prf

> |||
> compareLT : {x, y : Double} -> LT = compare x y -> So (x < y)
> compareLT {x} {y} p with (compare x y)
>   compareLT {x} {y} _ | LT = Oh
>   compareLT {x} {y} p | EQ = absurd p
>   compareLT {x} {y} p | GT = absurd p

> compareEQ : {x, y : Double} -> EQ = compare x y -> So (x == y)
> compareEQ {x} {y} p with (compare x y) proof prf
>   | LT = absurd p
>   | EQ with (decSo (x == y))
>     | (Yes q) = q
>     | (No  c) = void (notCompareEQ c prf)
>   | GT = absurd p

> compareEQ' : {x, y : Double} -> So (x == y) -> compare x y = EQ
> compareEQ' {x} {y} p with (x == y) proof q
>   | True  = Refl
>   | False = absurd p

> |||
> compareGT : {x, y : Double} -> GT = compare x y -> So (x > y)
> compareGT {x} {y} p with (compare x y)
>   compareGT {x} {y} p | LT = absurd p
>   compareGT {x} {y} p | EQ = absurd p
>   compareGT {x} {y} _ | GT = Oh


* 

> |||
> positiveImpliesNonNegative : {x : Double} -> Positive x -> NonNegative x
> positiveImpliesNonNegative (MkPositive prf) = MkNonNegative (LTinLTE prf) 

