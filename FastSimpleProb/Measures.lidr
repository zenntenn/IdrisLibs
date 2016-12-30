> module FastSimpleProb.Measures

> import Data.So

> import FastSimpleProb.SimpleProb
> import FastSimpleProb.BasicOperations
> import List.Operations

> -- import SimpleProb.MonadicOperations

> %default total
> %access public export
> %auto_implicits off


> |||
> average : SimpleProb Double -> Double
> average = sumProds . toList 


> ||| |average| is monotone
> postulate monotoneAverage : {A : Type} ->
>                             (f : A -> Double) -> (g : A -> Double) ->
>                             (p : (a : A) -> So (f a <= g a)) ->
>                             (as : SimpleProb A) ->
>                             So (average (fmap f as) <= average (fmap g as))
 
