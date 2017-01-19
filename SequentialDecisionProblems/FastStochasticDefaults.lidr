> module SequentialDecisionProblems.FastStochasticDefaults

> import SequentialDecisionProblems.CoreTheory
> import SequentialDecisionProblems.Utils

> import FastSimpleProb.SimpleProb
> import FastSimpleProb.MonadicOperations
> import FastSimpleProb.MonadicProperties

> %default total
> %auto_implicits off


In stochastic SDPs, |M = SimpleProb|:

> SequentialDecisionProblems.CoreTheory.M =  
>   SimpleProb

Thus, |M| is a functor:

> SequentialDecisionProblems.CoreTheory.fmap =  
>   FastSimpleProb.MonadicOperations.fmap

, |M| is a monad:

> SequentialDecisionProblems.Utils.ret =
>   FastSimpleProb.MonadicOperations.ret

> SequentialDecisionProblems.Utils.bind =
>   FastSimpleProb.MonadicOperations.bind

Moreover, |M| is a container monad

> SequentialDecisionProblems.CoreTheory.Elem =
>   FastSimpleProb.MonadicOperations.Elem

> SequentialDecisionProblems.CoreTheory.NotEmpty =
>   FastSimpleProb.MonadicOperations.NonEmpty

> SequentialDecisionProblems.CoreTheory.All =
>   FastSimpleProb.MonadicOperations.All

> SequentialDecisionProblems.CoreTheory.elemNotEmptySpec0 =
>   FastSimpleProb.MonadicProperties.elemNonEmptySpec0

> SequentialDecisionProblems.CoreTheory.elemNotEmptySpec1 =
>   FastSimpleProb.MonadicProperties.elemNonEmptySpec1

> SequentialDecisionProblems.CoreTheory.tagElem = 
>   FastSimpleProb.MonadicOperations.tagElem

> SequentialDecisionProblems.CoreTheory.allElemSpec0 =
>   FastSimpleProb.MonadicProperties.containerMonadSpec3

and |All| and |NotEmpty| are finite and decidable:

> SequentialDecisionProblems.Utils.finiteAll = 
>   FastSimpleProb.MonadicProperties.finiteAll

> SequentialDecisionProblems.Utils.finiteNotEmpty = 
>   FastSimpleProb.MonadicProperties.finiteNonEmpty

> SequentialDecisionProblems.Utils.decidableAll = 
>   FastSimpleProb.MonadicProperties.decidableAll

> SequentialDecisionProblems.Utils.decidableNotEmpty = 
>   FastSimpleProb.MonadicProperties.decidableNonEmpty


> {-

> ---}

