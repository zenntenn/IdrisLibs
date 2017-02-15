> module FastSimpleProb.Predicates

> import FastSimpleProb.SimpleProb
> import FastSimpleProb.MonadicOperations
> import NonNegDouble.NonNegDouble
> import NonNegDouble.Predicates
> import Functor.Predicates

> %default total
> %access public export
> %auto_implicits off


> {-
> ||| Monotonicity of |SimpleProb| measures
> Monotone : (SimpleProb NonNegDouble -> NonNegDouble) -> Type
> Monotone meas = {A : Type} -> 
>                 (f : A -> NonNegDouble) -> (g : A -> NonNegDouble) ->
>                 (p : (a : A) -> f a `LTE` g a) -> (sp : SimpleProb A) ->
>                 meas (fmap f sp) `LTE` meas (fmap g sp)
> Monotone = Functor.Predicates.Monotone {B = NonNegDouble} {C = NonNegDouble} {F = SimpleProb} LTE LTE 
> -}
