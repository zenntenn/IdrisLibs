> module SequentialDecisionProblems.FullTheoryOptDefaults

> import SequentialDecisionProblems.CoreTheory
> import SequentialDecisionProblems.FullTheory
> import SequentialDecisionProblems.Utils
> import SequentialDecisionProblems.CoreTheoryOptDefaults

> import Finite.Predicates
> import Finite.Operations
> import Opt.Operations
> import Rel.TotalPreorder

> %default total
> %access public export
> %auto_implicits off


> SequentialDecisionProblems.FullTheory.cvalmax {n} x r v ps =
>  Opt.Operations.max totalPreorderLTE (finiteGoodCtrl n x) (cardNotZGoodCtrl n x v) (cval x r v ps)

> SequentialDecisionProblems.FullTheory.cvalmaxSpec {n} x r v ps = 
>   Opt.Operations.maxSpec totalPreorderLTE (finiteGoodCtrl n x) (cardNotZGoodCtrl n x v) (cval x r v ps)

> SequentialDecisionProblems.FullTheory.cvalargmaxSpec {n} x r v ps =
>   Opt.Operations.argmaxSpec totalPreorderLTE (finiteGoodCtrl n x) (cardNotZGoodCtrl n x v) (cval x r v ps)


> {-

> ---}
