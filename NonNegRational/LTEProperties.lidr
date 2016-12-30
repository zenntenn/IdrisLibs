> module NonNegRational.LTEProperties

> import Syntax.PreorderReasoning

> import NonNegRational.NonNegRational
> import NonNegRational.BasicOperations
> import NonNegRational.BasicProperties
> import NonNegRational.Predicates
> import Fraction.Fraction
> import Fraction.BasicOperations
> import Fraction.Predicates
> import Fraction.BasicProperties
> import Fraction.Normalize
> import Fraction.NormalizeProperties
> import Fraction.EqProperties
> import Fraction.LTEProperties
> import Fraction.Normal
> import Subset.Properties
> import Unique.Predicates
> import Nat.Positive
> import Num.Refinements
> import Pairs.Operations
> import Nat.LTEProperties
> import Nat.OperationsProperties
> -- import ListProperties 
> import Rel.TotalPreorder 

> %default total
> %access public export


|LTE| is a total preorder:

> ||| LTE is reflexive
> reflexiveLTE : (x : NonNegRational) -> x `LTE` x
> reflexiveLTE x = reflexiveLTE (toFraction x)
> %freeze reflexiveLTE


> ||| LTE is transitive
> transitiveLTE : (x, y, z : NonNegRational) -> x `LTE` y -> y `LTE` z -> x `LTE` z
> transitiveLTE x y z xLTEy yLTEz = transitiveLTE (toFraction x) (toFraction y) (toFraction z) xLTEy yLTEz
> %freeze transitiveLTE


> ||| LTE is total
> totalLTE : (x, y : NonNegRational) -> Either (x `LTE` y) (y `LTE` x) 
> totalLTE x y = totalLTE (toFraction x) (toFraction y)
> %freeze totalLTE


> ||| LTE is a total preorder
> totalPreorderLTE : TotalPreorder NonNegRational.Predicates.LTE
> totalPreorderLTE = MkTotalPreorder LTE reflexiveLTE transitiveLTE totalLTE


Properties of |LTE| and |plus|:

> ||| LTE is monotone w.r.t. `plus`
> monotonePlusLTE : {a, b, c, d : NonNegRational} -> 
>                   a `LTE` b -> c `LTE` d -> (a + c) `LTE` (b + d)
> monotonePlusLTE {a} {b} {c} {d} aLTEb cLTEd = s4 where
>   s1 : LTE (toFraction a + toFraction c) (toFraction b + toFraction d)
>   s1 = Fraction.LTEProperties.monotonePlusLTE aLTEb cLTEd
>   s2 : LTE (normalize (toFraction a + toFraction c)) 
>            (normalize (toFraction b + toFraction d))
>   s2 = normalizeLTELemma (toFraction a + toFraction c) (toFraction b + toFraction d) s1
>   s3 : LTE (toFraction (fromFraction (toFraction a + toFraction c)))
>            (toFraction (fromFraction (toFraction b + toFraction d)))
>   s3 = s2
>   s4 : LTE (fromFraction (toFraction a + toFraction c)) (fromFraction (toFraction b + toFraction d))
>   s4 = s3
>   s5 : LTE (a + c) (b + d)
>   s5 = s4
> %freeze monotonePlusLTE


Properties of |LTE| and |mult|:

> ||| LTE is monotone w.r.t. `(*)`
> monotoneMultLTE : {a, b, c, d : NonNegRational} -> 
>                   a `LTE` b -> c `LTE` d -> (a * c) `LTE` (b * d)
> monotoneMultLTE {a} {b} {c} {d} aLTEb cLTEd = s4 where
>   s1 : LTE (toFraction a * toFraction c) (toFraction b * toFraction d)
>   s1 = Fraction.LTEProperties.monotoneMultLTE aLTEb cLTEd
>   s2 : LTE (normalize (toFraction a * toFraction c)) 
>            (normalize (toFraction b * toFraction d))
>   s2 = normalizeLTELemma (toFraction a * toFraction c) (toFraction b * toFraction d) s1
>   s3 : LTE (toFraction (fromFraction (toFraction a * toFraction c)))
>            (toFraction (fromFraction (toFraction b * toFraction d)))
>   s3 = s2
>   s4 : LTE (fromFraction (toFraction a * toFraction c)) (fromFraction (toFraction b * toFraction d))
>   s4 = s3
>   s5 : LTE (a * c) (b * d)
>   s5 = s4
> %freeze monotoneMultLTE


> {-

> ---}
 
