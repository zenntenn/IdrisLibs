> module FastSimpleProb.Measures

> import Data.So

> import FastSimpleProb.SimpleProb
> import FastSimpleProb.BasicOperations
> import FastSimpleProb.MonadicOperations
> import NonNegDouble.NonNegDouble
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
>                             (p : (a : A) -> So (f a <= g a)) ->
>                             (as : SimpleProb A) ->
>                             So (average (fmap f as) <= average (fmap g as))
 
 
