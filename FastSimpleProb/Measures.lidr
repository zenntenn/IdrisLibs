> module FastSimpleProb.Measures

> import FastSimpleProb.SimpleProb
> import FastSimpleProb.BasicOperations
> import FastSimpleProb.MonadicOperations
> import FastSimpleProb.MonadicPostulates
> import FastSimpleProb.MonadicProperties
> import Double.Predicates
> import NonNegDouble.NonNegDouble
> import NonNegDouble.Predicates
> import NonNegDouble.BasicOperations
> import NonNegDouble.Operations
> import NonNegDouble.Properties
> import NonNegDouble.Measures
> import NonNegDouble.LTEProperties
> import List.Operations
> import List.Properties
> import Fun.Operations
> import Rel.TotalPreorder
> import Pairs.Operations

> %default total
> %access public export
> %auto_implicits off


* Measures

> ||| Worst
> worst : SimpleProb NonNegDouble -> NonNegDouble
> worst sp = List.Operations.min totalPreorderLTE xs ne where
>   xs : List NonNegDouble
>   xs = map fst (toList sp)
>   ne : List.Operations.NonEmpty xs
>   ne = mapPreservesNonEmpty fst (toList sp) (nonEmptyLemma1 sp)

> ||| Sum
> sum : SimpleProb NonNegDouble -> NonNegDouble
> sum = Prelude.Foldable.sum . (map (uncurry (*))) . toList

> ||| Expected value
> expectedValue : SimpleProb NonNegDouble -> NonNegDouble
> expectedValue = sum . normalize


> {-


> ---}
