> module SequentialDecisionProblems.StochasticDefaults

> -- import Data.List
> -- import Data.List.Quantifiers

> import SequentialDecisionProblems.CoreTheory
> import SequentialDecisionProblems.Utils

> import SimpleProb.SimpleProb
> import SimpleProb.MonadicOperations
> import SimpleProb.MonadicProperties
> -- import List.Operations
> -- import List.Properties

> %default total
> %auto_implicits off


In stochastic SDPs, |M = SimpleProb|:

> SequentialDecisionProblems.CoreTheory.M =  
>   SimpleProb

Thus, |M| is a functor:

> SequentialDecisionProblems.CoreTheory.fmap =  
>   SimpleProb.MonadicOperations.fmap

, |M| is a monad:

> SequentialDecisionProblems.Utils.ret =
>   SimpleProb.MonadicOperations.ret

> SequentialDecisionProblems.Utils.bind =
>   SimpleProb.MonadicOperations.bind

Moreover, |M| is a container monad

> SequentialDecisionProblems.CoreTheory.Elem =
>   SimpleProb.MonadicOperations.Elem

> SequentialDecisionProblems.CoreTheory.NotEmpty =
>   SimpleProb.MonadicOperations.NonEmpty

> SequentialDecisionProblems.CoreTheory.All =
>   SimpleProb.MonadicOperations.All

> SequentialDecisionProblems.CoreTheory.elemNotEmptySpec0 =
>   SimpleProb.MonadicProperties.elemNonEmptySpec0

> SequentialDecisionProblems.CoreTheory.elemNotEmptySpec1 =
>   SimpleProb.MonadicProperties.elemNonEmptySpec1

> SequentialDecisionProblems.CoreTheory.tagElem = 
>   SimpleProb.MonadicOperations.tagElem

> SequentialDecisionProblems.CoreTheory.allElemSpec0 =
>   SimpleProb.MonadicProperties.containerMonadSpec3

and |All| and |NotEmpty| are finite and decidable:

> SequentialDecisionProblems.Utils.finiteAll = 
>   SimpleProb.MonadicProperties.finiteAll

> SequentialDecisionProblems.Utils.finiteNotEmpty = 
>   SimpleProb.MonadicProperties.finiteNonEmpty

> SequentialDecisionProblems.Utils.decidableAll = 
>   SimpleProb.MonadicProperties.decidableAll

> SequentialDecisionProblems.Utils.decidableNotEmpty = 
>   SimpleProb.MonadicProperties.decidableNonEmpty


> {-

> ---}

