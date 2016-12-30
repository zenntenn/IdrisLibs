> module FastSimpleProb.BasicOperations

> import Data.List
> import Data.So

> import FastSimpleProb.SimpleProb
> import Double.Predicates
> import NonNegDouble.NonNegDouble
> import NonNegDouble.BasicOperations
> import NonNegDouble.BasicProperties
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
>   psum' = ?kuka


> {-

> |||
> weights : {A : Type} -> SimpleProb A -> List Double
> weights sp = map snd (toList sp)


> ||| 'weight sp a' is the weight of 'a' according to 'sp'
> weight : {A : Type} -> (Eq A) => SimpleProb A -> A -> Double
> weight sp a = foldr f 0.0 (toList sp) where
>   f : (A, Double) -> Double -> Double
>   f (a', w') w = if (a == a') then w + w' else w


> ||| 'prob sp a' is the probability of 'a' according to 'sp'
> prob : {A : Type} -> (Eq A) => SimpleProb A -> A -> Double
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
> mkSimpleProb      Nil            prf = absurd prf
> mkSimpleProb {A} (a :: Nil)      _   = Ret (a, Element 1.0 Oh)
> mkSimpleProb {A} (a :: a' :: as) _   = (a, Element 1.0 Oh) :: (mkSimpleProb (a' :: as) ())


> ---}    




