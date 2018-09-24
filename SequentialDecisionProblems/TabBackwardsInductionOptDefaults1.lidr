> module SequentialDecisionProblems.TabBackwardsInductionOptDefaults1

> import Data.Vect

> import SequentialDecisionProblems.CoreTheory
> import SequentialDecisionProblems.TabBackwardsInduction1
> import SequentialDecisionProblems.Utils
> import SequentialDecisionProblems.CoreTheoryOptDefaults

> import Finite.Predicates
> import Finite.Operations
> import Opt.Operations
> import Rel.TotalPreorder

> %default total
> %access public export
> %auto_implicits off


> SequentialDecisionProblems.TabBackwardsInduction1.tcvalargmax {n} x r v ps =
>   Opt.Operations.argmax totalPreorderLTE (finiteGoodCtrl n x) (cardNotZGoodCtrl n x v) (tcval x r v ps)

> {-

> ---}
