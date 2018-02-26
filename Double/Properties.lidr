> module Double.Properties

> import Data.So

> import Double.Predicates
> import Double.Postulates
> import Double.Operations
> import So.Properties
> import Ordering.Properties
> import Rel.TotalPreorder
> import So.Properties

> %default total
> %access public export
> %auto_implicits on


* Decidability of EQ

> |||
> decEQ : (x : Double) -> (y : Double) -> Dec (x `EQ` y)
> decEQ x y with (decSo (x == y))
>   | Yes p = Yes (MkEQ p)
>   | No contra = No (\ (MkEQ p) => contra p)


* Properties of Ord methods

> |||
> LTinLTE : {x, y : Double} -> So (x < y) -> So (x <= y)
> LTinLTE {x} {y} prf = soOrIntro1 (x < y) (x == y) prf
> -- LTinLTE : {x, y : Double} -> x `LT` y -> x `LTE` y
> -- LTinLTE {x} {y} (MkLT prf) = MkLTE (soOrIntro1 (x < y) (x == y) prf)

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


* LT, LTE:

> ||| LTE is total
> totalLTE : (x, y : Double) -> Either (x `LTE` y) (y `LTE` x) 
> totalLTE x y with (compare x y) proof prf
>   | LT = Left  (MkLTE (LTinLTE (compareLT prf)))
>   | EQ = Left  (MkLTE (EQinLTE (compareEQ prf)))
>   | GT = Right (MkLTE (LTinLTE (gtLT (compareGT prf))))

> ||| LTE is a total preorder
> totalPreorderLTE : TotalPreorder Double.Predicates.LTE
> totalPreorderLTE = MkTotalPreorder LTE reflexiveLTE transitiveLTE totalLTE

> ||| LT is decidable
> decLT : (x : Double) -> (y : Double) -> Dec (x `LT` y)
> decLT x y with (decSo (x < y))
>   | Yes prf    = Yes (MkLT prf)
>   |  No contra =  No (\ (MkLT prf) => void (contra prf))

> ||| LTE is decidable
> decLTE : (x : Double) -> (y : Double) -> Dec (x `LTE` y)
> decLTE x y with (decSo (x <= y))
>   | Yes prf    = Yes (MkLTE prf)
>   |  No contra =  No (\ (MkLTE prf) => void (contra prf))

> |||
> minusLTELemma : (x : Double) -> (y : Double) ->
>                 x `LTE` y -> 0.0 `LTE` y - x 
> minusLTELemma x y xLTEy = s2 where
>   s1 : x - x `LTE` y - x
>   s1 = monotoneMinusConstLTE xLTEy
>   s2 : 0.0 `LTE` y - x
>   s2 = replace {P = \ X => X `LTE` y - x} (minusSelfZero) s1

> |||
> divLTELemma : (x : Double) -> (y : Double) -> x `LTE` y -> 
>               Positive y -> x / y `LTE` 1.0
> divLTELemma x y xLTEy py = s2 where
>   s1 : x / y `LTE` y / y
>   s1 = monotoneDivConstLTE xLTEy py
>   s2 : x / y `LTE` 1.0
>   s2 = replace {P = \ X => x / y `LTE` X} (divPositiveSelfOne py) s1
  
> |||
> divNonNegativePositiveNonNegative : (x : Double) -> (y : Double) ->
>                                     0.0 `LTE` x -> Positive y ->
>                                     0.0 `LTE` x / y
> divNonNegativePositiveNonNegative x y zLTEx py = s2 where
>   s1 : 0.0 / y `LTE` x / y
>   s1 = monotoneDivConstLTE zLTEx py
>   s2 : 0.0 `LTE` x / y
>   s2 = replace {P = \ X => X `LTE` x / y} (divZeroPositiveZero py) s1

> ||| |sum| is monotone
> monotoneSum : {A : Type} ->
>               (f : A -> Double) -> (g : A -> Double) ->
>               (p : (a : A) -> f a `LTE` g a) ->
>               (as : List A) ->
>               sum (map f as) `LTE` sum (map g as)
> monotoneSum f g p Nil = reflexiveLTE 0.0               
> monotoneSum f g p (a :: as) = 
>   monotonePlusLTE {a = f a} {b = g a} {c = sum (map f as)} {d = sum (map g as)} (p a) (monotoneSum f g p as)


* Non-negative double precision floating point numbers:

> ||| Non-negative |Double|s are closed w.r.t. sum
> plusPreservesNonNegativity : {x, y : Double} -> 
>                              NonNegative x -> NonNegative y -> NonNegative (x + y) 
> plusPreservesNonNegativity {x} {y} zeroLTEx zeroLTEy = s2 where
>   s1 : 0.0 + 0.0 `LTE` x + y
>   s1 = monotonePlusLTE {a = 0.0} {b = x} {c = 0.0} {d = y} zeroLTEx zeroLTEy
>   s2 : 0.0 `LTE` x + y
>   s2 = replace {P = \ X => X `LTE` x + y} plusZeroLeftNeutral s1

> ||| Non-negative |Double|s are closed w.r.t. multiplication
> multPreservesNonNegativity : {x, y : Double} -> 
>                              NonNegative x -> NonNegative y -> NonNegative (x * y)
> multPreservesNonNegativity {x} {y} zeroLTEx zeroLTEy = s2 where
>   s1 : 0.0 * 0.0 `LTE` x * y
>   s1 = monotoneMultLTE {a = 0.0} {b = x} {c = 0.0} {d = y} zeroLTEx zeroLTEy
>   s2 : 0.0 `LTE` x * y
>   s2 = replace {P = \ X => X `LTE` x * y} (multZeroLeftZero {x = 0.0}) s1


* Positive double precision floating point numbers:

> |||
> positiveImpliesNonNegative : {x : Double} -> Positive x -> NonNegative x
> positiveImpliesNonNegative (MkLT prf) = MkLTE (LTinLTE prf) 


* Properties of constants:

> ||| one is not zero
> notOneEqZero : Not (1.0 = 0.0)
> notOneEqZero Refl impossible

> ||| zero is not positive
> notPositiveZero : Not (Positive 0.0)
> notPositiveZero (MkLT prf) = contra Refl prf


* Properties of |fromNat|

> |||
> fromNatNonNegative : {n : Nat} -> NonNegative (fromNat n)
> fromNatNonNegative {n = Z}   = MkLTE Oh
> fromNatNonNegative {n = S m} = plusPreservesNonNegativity (MkLTE Oh) fromNatNonNegative 

> |||
> fromSuccPositive : {n : Nat} -> Positive (fromNat (S n))
> fromSuccPositive {n} = positivePlusAnyPositive (MkLT Oh) fromNatNonNegative  


* Convexity

> |||
> convexLemma1 : (x1 : Double) -> (x2 : Double) -> Positive (x2 - x1) ->
>                (x : Double) -> (q : x1 `LTE` x) ->
>                0.0 `LTE` (x - x1) / (x2 - x1)
> convexLemma1 x1 x2 px2mx1 x x1LTEx = 
>   divNonNegativePositiveNonNegative (x - x1) (x2 - x1) s1 px2mx1 where
>     s1 : 0.0 `LTE` (x - x1)
>     s1 = minusLTELemma x1 x x1LTEx

> |||
> convexLemma2 : (x1 : Double) -> (x2 : Double) -> Positive (x2 - x1) ->
>                (x : Double) -> (q : x `LTE` x2) ->
>                (x - x1) / (x2 - x1) `LTE` 1.0
> convexLemma2 x1 x2 px2mx1 x q = divLTELemma (x - x1) (x2 - x1) s1 px2mx1 where
>   s1 : (x - x1) `LTE` (x2 - x1)
>   s1 = monotoneMinusConstLTE q  

> |||
> convexLemma : (x1 : Double) -> (x2 : Double) -> (alpha : Double) ->
>               NonNegative x1 -> NonNegative x2 -> 
>               0.0 `LTE` alpha -> alpha `LTE` 1.0 ->
>               NonNegative (x1 * (1.0 - alpha) + x2 * alpha)
> convexLemma x1 x2 alpha nnx1 nnx2 (MkLTE p1) (MkLTE p2) = s4 where
>   s1 : NonNegative alpha
>   s1 = MkLTE p1
>   s2 : alpha - alpha `LTE` 1.0 - alpha
>   s2 = monotoneMinusConstLTE (MkLTE p2)
>   s3 : NonNegative (1.0 - alpha)
>   s3 = replace {P = \ X => X `LTE` 1.0 - alpha} minusSelfZero s2
>   s4 : NonNegative (x1 * (1.0 - alpha) + x2 * alpha)
>   s4 = plusPreservesNonNegativity {x = x1 * (1.0 - alpha)} {y = x2 * alpha}
>                                   (multPreservesNonNegativity nnx1 s3)
>                                   (multPreservesNonNegativity nnx2 s1)


* Properties of |mkLinearStepLemma|:

> |||
> mkLinearStepLemma : (x1 : Double) -> (x2 : Double) -> Positive (x2 - x1) ->
>                     (y1 : Double) -> (y2 : Double) -> 
>                     NonNegative y1 -> NonNegative y2 ->   
>                     (x : Double) -> NonNegative (mkLinearStep x1 x2 prf y1 y2 x)
> mkLinearStepLemma x1 x2 px2mx1 y1 y2 nny1 nny2 x with (decSo (x < x1))
>   | Yes _ = nny1
>   | No  _ with (decSo (x1 <= x && x <= x2))
>     | Yes prf = s3 where
>         alpha : Double
>         alpha = (x - x1) / (x2 - x1)
>         s1 : 0.0 `LTE` alpha
>         s1 = convexLemma1 x1 x2 px2mx1 x (MkLTE (soAndElim1 (x1 <= x) (x <= x2) prf))
>         s2 : alpha `LTE` 1.0
>         s2 = convexLemma2 x1 x2 px2mx1 x (MkLTE (soAndElim2 (x1 <= x) (x <= x2) prf))
>         s3 : NonNegative (y1 * (1.0 - alpha) + y2 * alpha)
>         s3 = convexLemma y1 y2 alpha nny1 nny2 s1 s2
>     | No _ = nny2


> {-

> ---}
