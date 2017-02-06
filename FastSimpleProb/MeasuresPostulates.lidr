> module FastSimpleProb.MonadicPostulates

> import FastSimpleProb.SimpleProb
> import FastSimpleProb.BasicOperations
> import FastSimpleProb.MonadicOperations
> import FastSimpleProb.Predicates
> import FastSimpleProb.Measures
> import Double.Predicates
> import NonNegDouble.NonNegDouble
> import NonNegDouble.Predicates

> %default total
> %access public export
> %auto_implicits off


> postulate
> monotoneWorst : (A : Type) ->
>                 (f : A -> NonNegDouble) -> (g : A -> NonNegDouble) ->
>                 (p : (a : A) -> f a `LTE` g a) ->
>                 (sp : SimpleProb A) ->
>                 worst (fmap f sp) `LTE` worst (fmap g sp)


 
