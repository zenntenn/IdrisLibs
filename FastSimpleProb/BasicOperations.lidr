> module FastSimpleProb.BasicOperations

> import Data.List
> import Data.So

> import FastSimpleProb.SimpleProb
> import Double.Predicates
> import NonNegDouble.NonNegDouble
> import NonNegDouble.Constants
> import NonNegDouble.BasicOperations
> import NonNegDouble.BasicProperties
> import NonNegDouble.Postulates
> import List.Operations
> import Fun.Operations

> %default total
> %access public export
> %auto_implicits off


> |||
> toList : {A : Type} -> SimpleProb A -> List (A, NonNegDouble)
> toList (MkSimpleProb aps _) = aps


> |||
> support : {A : Type} -> SimpleProb A -> List A
> support = (map fst) . toList


> |||
> rescale : {A : Type} -> 
>           SimpleProb A -> (p : NonNegDouble) -> Positive (toDouble p) -> SimpleProb A
> rescale {A} (MkSimpleProb aps psum) p pp = MkSimpleProb aps' psum' where
>   aps'  : List (A, NonNegDouble)
>   aps'  = mapIdRightMult (aps, p)
>   psum' : Positive (toDouble (sumMapSnd aps'))
>   psum' = mapIdRightMultPreservesPositivity aps psum p pp


> |||
> normalize : {A : Type} -> 
>             SimpleProb A -> SimpleProb A
> normalize {A} (MkSimpleProb aps psum) = rescale (MkSimpleProb aps psum) oosum poosum where
>   sum    : NonNegDouble
>   sum    = sumMapSnd aps
>   oosum  : NonNegDouble
>   oosum  = oneNonNegDouble / sum
>   poosum : Positive (toDouble oosum)
>   poosum = divPreservesPositivity positiveOneNonNegDouble psum


> |||
> weights : {A : Type} -> SimpleProb A -> List NonNegDouble
> weights = (map snd) . toList


> ||| 'weight sp a' is the weight of 'a' according to 'sp'
> weight : {A : Type} -> (Eq A) => SimpleProb A -> A -> NonNegDouble
> weight sp a = foldr f (fromInteger 0) (toList sp) where
>   f : (A, NonNegDouble) -> NonNegDouble -> NonNegDouble
>   f (a', w') w = if (a == a') then w + w' else w


> ||| 'prob sp a' is the probability of 'a' according to 'sp'
> prob : {A : Type} -> (Eq A) => SimpleProb A -> A -> NonNegDouble
> prob sp a = (weight sp a) / (sum (weights sp))

> {-
> ||| 'prob sp a' is the probability of 'a' according to 'sp'
> prob : {A : Type} -> (Eq A) => SimpleProb A -> A -> Double
> prob sp a = fst pq / snd pq where
>   f : (A, Double) -> (Double, Double) -> (Double, Double)
>   f (a', p') (p, q) = if (a == a') then (p + p', q + p') else (p, q + p')
>   pq : (Double, Double)
>   pq = foldr f (0.0, 0.0) (toList sp)
> -}


> ||| Make a SimpleProb in which all elements of a list have the same 
> ||| probablility. If the list has no duplicates, this results in a
> ||| uniform probability distribution
> mkSimpleProb : {A : Type} -> (as : List A) -> List.Operations.NonEmpty as -> SimpleProb A
> mkSimpleProb      Nil              prf = absurd prf
> mkSimpleProb {A} (a :: Nil)        _   = MkSimpleProb [(a, oneNonNegDouble)] positiveOneNonNegDouble
> mkSimpleProb {A} (a :: (a' :: as)) _   = MkSimpleProb aps prf where
>   ps' : SimpleProb A
>   ps' = assert_total (mkSimpleProb (a' :: as) ())
>   aps : List (A, NonNegDouble)
>   aps = (a, oneNonNegDouble) :: (toList ps')
>   prf : Positive (toDouble (sumMapSnd aps))
>   prf = sumMapSndConsLemma1 a 1.0 positiveOneNonNegDouble (MkNonNegative Oh) (toList ps')


> {-

> ---}    




