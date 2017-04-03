> module FastSimpleProb.SimpleProb

> import Data.So

> import Double.Predicates
> import NonNegDouble.NonNegDouble
> import NonNegDouble.BasicOperations
> import NonNegDouble.Properties
> import List.Operations

> %default total
> %access public export
> %auto_implicits off


> |||
> data SimpleProb : Type -> Type where
>   MkSimpleProb : {A : Type} -> 
>                  (aps : List (A, NonNegDouble)) -> 
>                  Positive (toDouble (sumMapSnd aps)) ->
>                  SimpleProb A

