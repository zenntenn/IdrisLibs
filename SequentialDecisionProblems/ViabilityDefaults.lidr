> module SequentialDecisionProblems.ViabilityDefaults

> import SequentialDecisionProblems.CoreTheory
> import SequentialDecisionProblems.Utils

> import Unit.Properties

> %default total
> %auto_implicits off


This is the default implementation of |Viable|: all states are viable
for 0 steps; a state is viable for |n + 1| steps iff it has a control
such that 1) the set of next possible states is not empty and 2) all
next possible states are viable for |n| steps. These two conditions are
encoded in the notion of "good" control, see |Utils|:

> -- Viable : (n : Nat) -> State t -> Type
> SequentialDecisionProblems.CoreTheory.Viable {t}  Z    _ = Unit
> SequentialDecisionProblems.CoreTheory.Viable {t} (S n) x = GoodCtrl t x n

Trivially, for every state that is viable for |n + 1| steps we can
compute a good control

> -- viableSpec0 : (x : State t) -> Viable Z x
> SequentialDecisionProblems.CoreTheory.viableSpec0 x = ()

> -- viableSpec1 : (x : State t) -> Viable (S n) x -> GoodCtrl t x n
> SequentialDecisionProblems.CoreTheory.viableSpec1 {t} {n} x v = v

> -- viableSpec2 : (x : State t) -> GoodCtrl t x n -> Viable (S n) x
> SequentialDecisionProblems.CoreTheory.viableSpec2 {t} {n} x gy = gy


If users can show that ..., see |Utils|. For |M = List|, for instance,
... are implemented in |NonDeterministic Defaults|:

> -- finiteViable : {t : Nat} -> 
> --                (n : Nat) -> (x : State t) -> Finite (Viable n x)
> SequentialDecisionProblems.Utils.finiteViable Z     _ = finiteUnit
> SequentialDecisionProblems.Utils.finiteViable (S m) x = finiteGoodCtrl m x

> -- decidableViable : {t : Nat} -> 
> --                   (n : Nat) -> (x : State t) -> Dec (Viable n x)
> SequentialDecisionProblems.Utils.decidableViable  Z    _ = Yes MkUnit
> SequentialDecisionProblems.Utils.decidableViable (S m) x = decidableGoodCtrl m x


> {-

> ---}

