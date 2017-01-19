> module FastSimpleProb.Measures

> import Data.So

> import FastSimpleProb.SimpleProb
> import FastSimpleProb.BasicOperations
> import FastSimpleProb.MonadicOperations
> import NonNegDouble.NonNegDouble
> import NonNegDouble.Predicates
> import NonNegDouble.BasicProperties
> import List.Operations

> %default total
> %access public export
> %auto_implicits off


> |||
> average : SimpleProb NonNegDouble -> NonNegDouble
> average = sumProds . toList 


> ||| |average| is monotone
> postulate monotoneAverage : {A : Type} ->
>                             (f : A -> NonNegDouble) -> (g : A -> NonNegDouble) ->
>                             (p : (a : A) -> f a `LTE` g a) ->
>                             (sp : SimpleProb A) ->
>                             average (fmap f sp) `LTE` average (fmap g sp)
 
 
