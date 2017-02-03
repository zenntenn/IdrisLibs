> module FastSimpleProb.MonadicPostulates

> import FastSimpleProb.SimpleProb
> import FastSimpleProb.BasicOperations
> import FastSimpleProb.MonadicOperations
> import Double.Predicates
> import NonNegDouble.NonNegDouble
> import NonNegDouble.BasicOperations

> %default total
> %access public export
> %auto_implicits off


* On |fmap| and |rescale|:

> postulate
> fmapRescaleLemma : {A : Type} -> 
>                    (f : A -> NonNegDouble) ->
>                    (p : NonNegDouble) -> (pp : Positive (toDouble p)) -> 
>                    (sp : SimpleProb A) -> 
>                    rescale p pp (fmap f sp) = fmap f (rescale p pp sp)


* On |fmap| and |normalize|:

> postulate
> fmapNormalizeLemma : {A, B : Type} -> 
>                      (f : A -> B) ->
>                      (sp : SimpleProb A) -> 
>                      normalize (fmap f sp) = fmap f (normalize sp)


 
