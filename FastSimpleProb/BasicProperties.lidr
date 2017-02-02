> module FastSimpleProb.BasicProperties

> import Data.List

> import FastSimpleProb.SimpleProb
> import FastSimpleProb.BasicOperations
> import Double.Predicates
> import List.Operations
> import NonNegDouble.NonNegDouble
> import NonNegDouble.BasicOperations
> import NonNegDouble.BasicProperties
> import List.Operations
> import List.Properties

> %default total
> %access public export
> %auto_implicits on


* Properties of |toList|:

> |||
> toListLemma : {A : Type} -> (sp : SimpleProb A) -> Positive (toDouble (sumMapSnd (toList sp)))
> toListLemma (MkSimpleProb _ prf) = prf


* Properties of weights:

> |||
> positiveWeights : {A : Type} -> (sp : SimpleProb A) -> Positive (toDouble (sum (weights sp)))
> positiveWeights = toListLemma


> |||
> lengthSupportWeightsLemma : {A : Type} -> 
>                             (sp : SimpleProb A) ->
>                             length (support sp) = length (weights sp)
> lengthSupportWeightsLemma sp = lengthLemma (toList sp) fst snd                           


* Implementations:

> ||| SimpleProb is an implementation of Show
> implementation Show a => Show (SimpleProb a) where
>   show sp = show (toList sp)


> {-

> ---}    




