> module SequentialDecisionProblems.OptDefaults

> import SequentialDecisionProblems.CoreTheory
> import SequentialDecisionProblems.FullTheory
> import SequentialDecisionProblems.Utils

> import Finite.Predicates
> import Finite.Operations
> import Opt.Operations
> import Rel.TotalPreorder

> %default total
> %access public export
> %auto_implicits off


We implement |cvalmax|, |cvalargmax|, |cvalmaxSpec| and |cvalargmaxSpec|
by exhaustive search (see |Opt|) if we can show that |LTE| is a total
preorder

> totalPreorderLTE : TotalPreorder SequentialDecisionProblems.CoreTheory.LTE

, that |GoodCtrl t x n| is finite and that, for every |t : Nat|, |x :
State t| such that |Viable (S n) x|, its cardinality is not zero.

In typical applications, finiteness and non-emptyness of |GoodCtrl t x
n| are going to be deduced (see Utils) from finiteness of |All| and
|NotEmpty| (see, for instance, NonDeterministicDefaults), finiteness of
|Viable| (see ViabilityDefaults) and finiteness of controls.

> SequentialDecisionProblems.FullTheory.cvalmax {n} x r v ps =
>  Opt.Operations.max totalPreorderLTE (finiteGoodCtrl n x) (cardNotZGoodCtrl n x v) (cval x r v ps)

> SequentialDecisionProblems.CoreTheory.cvalargmax {n} x r v ps =
>   Opt.Operations.argmax totalPreorderLTE (finiteGoodCtrl n x) (cardNotZGoodCtrl n x v) (cval x r v ps)

> SequentialDecisionProblems.FullTheory.cvalmaxSpec {n} x r v ps = 
>   Opt.Operations.maxSpec totalPreorderLTE (finiteGoodCtrl n x) (cardNotZGoodCtrl n x v) (cval x r v ps)

> SequentialDecisionProblems.FullTheory.cvalargmaxSpec {n} x r v ps =
>   Opt.Operations.argmaxSpec totalPreorderLTE (finiteGoodCtrl n x) (cardNotZGoodCtrl n x v) (cval x r v ps)


> {-

> ---}
