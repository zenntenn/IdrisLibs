> module FastSimpleProb.BasicOperations

> import Data.List
> import Data.So
> import Syntax.PreorderReasoning

> import FastSimpleProb.SimpleProb
> import Double.Predicates
> import NonNegDouble.NonNegDouble
> import NonNegDouble.Constants
> import NonNegDouble.BasicOperations
> import NonNegDouble.Operations
> import NonNegDouble.Properties
> import NonNegDouble.Postulates
> import List.Operations
> import Fun.Operations
> import Pairs.Operations

> %default total
> %access public export
> %auto_implicits off


> |||
> mkSimpleProb : {A : Type} -> 
>                (aps : List (A, NonNegDouble)) -> 
>                {auto prf : Positive (toDouble (sumMapSnd aps))} ->
>                SimpleProb A
> mkSimpleProb aps {prf} = MkSimpleProb aps prf


> |||
> toList : {A : Type} -> SimpleProb A -> List (A, NonNegDouble)
> toList (MkSimpleProb aps _) = aps


> |||
> support : {A : Type} -> SimpleProb A -> List A
> support = (map fst) . toList


> |||
> rescale : {A : Type} -> 
>           (p : NonNegDouble) -> Positive (toDouble p) -> SimpleProb A -> SimpleProb A
> rescale {A} p pp (MkSimpleProb aps psum) = MkSimpleProb aps' psum' where
>   aps'  : List (A, NonNegDouble)
>   aps'  = mapIdRightMult (aps, p)
>   psum' : Positive (toDouble (sumMapSnd aps'))
>   psum' = mapIdRightMultPreservesPositivity aps psum p pp


> |||
> normalize : {A : Type} -> 
>             SimpleProb A -> SimpleProb A
> normalize (MkSimpleProb aps psum) = 
>   let p  : NonNegDouble
>          = one / (sumMapSnd aps) in
>   let pp : Positive (toDouble p)
>          = divPreservesPositivity positiveOne psum in 
>   rescale p pp (MkSimpleProb aps psum) 


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
> mkFlatSimpleProb : {A : Type} -> (as : List A) -> List.Operations.NonEmpty as -> SimpleProb A
> mkFlatSimpleProb      Nil              prf = absurd prf
> mkFlatSimpleProb {A} (a :: Nil)        _   = MkSimpleProb [(a, one)] positiveOne
> mkFlatSimpleProb {A} (a :: (a' :: as)) _   = MkSimpleProb aps prf where
>   ps' : SimpleProb A
>   ps' = assert_total (mkFlatSimpleProb (a' :: as) ())
>   aps : List (A, NonNegDouble)
>   aps = (a, one) :: (toList ps')
>   prf : Positive (toDouble (sumMapSnd aps))
>   prf = sumMapSndConsLemma1 a 1.0 positiveOne (MkLTE Oh) (toList ps')

> ||| 
> showlong : {A : Type} -> Show A => SimpleProb A -> String
> showlong sp = showlong (toList sp) 


> {-

> ---}    




