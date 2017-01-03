> module SequentialDecisionProblems.NonDeterministicDefaults

> import Data.List
> import Data.List.Quantifiers

> import SequentialDecisionProblems.CoreTheory
> import SequentialDecisionProblems.Utils

> import List.Operations
> import List.Properties

> %default total
> %auto_implicits off


In non-deterministic SDPs, |M = List|:

> SequentialDecisionProblems.CoreTheory.M =  
>   List

Thus, |M| is a functor:

> SequentialDecisionProblems.CoreTheory.fmap =  
>   List.Operations.fmap

, |M| is a monad:

> SequentialDecisionProblems.Utils.ret =
>   List.Operations.ret

> SequentialDecisionProblems.Utils.bind =
>   List.Operations.bind

Moreover, |M| is a container monad

> SequentialDecisionProblems.CoreTheory.Elem =
>   Data.List.Elem

> SequentialDecisionProblems.CoreTheory.NotEmpty =
>   List.Operations.NonEmpty

> SequentialDecisionProblems.CoreTheory.All =
>   Data.List.Quantifiers.All

> SequentialDecisionProblems.CoreTheory.elemNotEmptySpec0 =
>   List.Properties.elemNonEmptySpec0

> SequentialDecisionProblems.CoreTheory.elemNotEmptySpec1 =
>   List.Properties.elemNonEmptySpec1

> SequentialDecisionProblems.CoreTheory.tagElem = 
>   List.Operations.tagElem

> SequentialDecisionProblems.CoreTheory.allElemSpec0 =
>   List.Properties.containerMonadSpec3

and |All| and |NotEmpty| are finite and decidable:

> SequentialDecisionProblems.Utils.finiteAll = 
>   List.Properties.finiteAll

> SequentialDecisionProblems.Utils.finiteNotEmpty =
>   List.Properties.finiteNonEmpty

> SequentialDecisionProblems.Utils.decidableAll = 
>   List.Properties.decidableAll

> SequentialDecisionProblems.Utils.decidableNotEmpty =
>   List.Properties.decidableNonEmpty


> {-

> ---}

