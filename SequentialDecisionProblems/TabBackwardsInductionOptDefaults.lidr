> module SequentialDecisionProblems.TabBackwardsInductionOptDefaults

> import Data.Vect

> import SequentialDecisionProblems.CoreTheory
> import SequentialDecisionProblems.TabBackwardsInduction
> import SequentialDecisionProblems.Utils
> import SequentialDecisionProblems.CoreTheoryOptDefaults

> import Finite.Predicates
> import Finite.Operations
> import Opt.Operations
> import Rel.TotalPreorder

> %default total
> %access public export
> %auto_implicits off


> SequentialDecisionProblems.TabBackwardsInduction.tcvalargmax {n} x r v ps =
>   Opt.Operations.argmax totalPreorderLTE (finiteGoodCtrl n x) (cardNotZGoodCtrl n x v) (tcval x r v ps)

> {-

> ---}
