> module SequentialDecisionProblems.DeterministicDefaults

> import Control.Monad.Identity

> import SequentialDecisionProblems.CoreTheory
> import SequentialDecisionProblems.Utils

> import Identity.Operations
> import Identity.Properties

> %default total
> %auto_implicits off


In deterministic SDPs, |M = Identity|:

> SequentialDecisionProblems.CoreTheory.M =  
>   Identity

Thus, |M| is a functor:

> SequentialDecisionProblems.CoreTheory.fmap =  
>   Identity.Operations.fmap

, |M| is a monad:

> SequentialDecisionProblems.Utils.ret =
>   Identity.Operations.ret

> SequentialDecisionProblems.Utils.bind =
>   Identity.Operations.bind

Moreover, |M| is a container monad

> SequentialDecisionProblems.CoreTheory.Elem =
>   Identity.Operations.Elem

> SequentialDecisionProblems.CoreTheory.NotEmpty =
>   Identity.Operations.NonEmpty

> SequentialDecisionProblems.CoreTheory.All =
>   Identity.Operations.All

> SequentialDecisionProblems.CoreTheory.elemNotEmptySpec0 =
>   Identity.Properties.elemNonEmptySpec0

> SequentialDecisionProblems.CoreTheory.elemNotEmptySpec1 =
>   Identity.Properties.elemNonEmptySpec1

> SequentialDecisionProblems.CoreTheory.tagElem = 
>   Identity.Operations.tagElem

> SequentialDecisionProblems.CoreTheory.allElemSpec0 =
>   Identity.Properties.containerMonadSpec3

and |All| and |NotEmpty| are finite and decidable:

> SequentialDecisionProblems.Utils.finiteAll = 
>   Identity.Properties.finiteAll

> SequentialDecisionProblems.Utils.finiteNotEmpty = 
>   Identity.Properties.finiteNonEmpty

> SequentialDecisionProblems.Utils.decidableAll = 
>   Identity.Properties.decidableAll

> SequentialDecisionProblems.Utils.decidableNotEmpty = 
>   Identity.Properties.decidableNonEmpty


> {-

> ---}

