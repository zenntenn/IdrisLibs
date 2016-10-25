> module SimpleProb.Measures

> import SimpleProb.SimpleProb
> import SimpleProb.BasicOperations
> import NonNegRational.NonNegRational
> import NonNegRational.BasicOperations
> import NonNegRational.BasicProperties
> import List.Operations

> -- postulate monotoneAverage
> import NonNegRational.Predicates
> import SimpleProb.MonadicOperations

> %default total
> %access public export
> %auto_implicits off


> |||
> average : SimpleProb NonNegRational -> NonNegRational
> average = sumProds . toList 


> ||| |average| is monotone
> postulate monotoneAverage : {A : Type} ->
>                             (f : A -> NonNegRational) -> (g : A -> NonNegRational) ->
>                             (p : (a : A) -> f a `LTE` g a) ->
>                             (as : SimpleProb A) ->
>                             average (fmap f as) `LTE` average (fmap g as) 
