> module SequentialDecisionProblems.TabBackwardsInductionOptDefaults2

> import Data.Vect

> import SequentialDecisionProblems.CoreTheory
> import SequentialDecisionProblems.TabBackwardsInduction2
> import SequentialDecisionProblems.Utils
> import SequentialDecisionProblems.CoreTheoryOptDefaults

> import Finite.Predicates
> import Finite.Operations
> import Finite.Properties
> import Opt.Operations
> import Rel.TotalPreorder
> import Sigma.Sigma
> import Sigma.Operations
> import Sigma.Properties
> import Vect.Operations
> import Vect.Properties
> import Decidable.Predicates

> %default total
> %access public export
> %auto_implicits off


> SequentialDecisionProblems.TabBackwardsInduction2.tabCvalargmaxMax {n} x r v ps =
>   Opt.Operations.argmaxMax totalPreorderLTE (finiteGoodCtrl n x) (cardNotZGoodCtrl n x v) (tabCval x r v ps)

> SequentialDecisionProblems.TabBackwardsInduction2.tabCvalargmax {n} x r v ps =
>   Opt.Operations.argmax totalPreorderLTE (finiteGoodCtrl n x) (cardNotZGoodCtrl n x v) (tabCval x r v ps)

> |||
> goodCtrl : {t, m : Nat} ->
>            (x : State t) -> .(r : Reachable x) -> .(v : Viable (S m) x) ->
>            PolicyTable t (S m) -> GoodCtrl t x m
> goodCtrl {t} {m} x r v pt =
>   let xs   : Vect (cardState t) (State t)
>            = vectState t in   
>   let prf  : Elem x xs
>            = toVectComplete (finiteState t) x in
>   let rvxs : Vect (cardReachableAndViableState t (S m)) (State t)
>            = map outl (vectReachableAndViableState t (S m)) in
>   let dRV  : ((x : State t) -> Dec (ReachableAndViable (S m) x))
>            = decidableReachableAndViable (S m) in                  
>   let prf' : Elem x rvxs
>            = filterTagSigmaLemma {P = ReachableAndViable (S m)} dRV x xs prf (r,v) in
>   let k    : Fin (cardReachableAndViableState t (S m))
>            = lookup x rvxs prf' in
>   let x'   : State t
>            = outl (index k pt) in
>   let gy'  : GoodCtrl t x' m 
>            = snd (outr (index k pt)) in
>   let gy   : GoodCtrl t x m
>            = replace {P = \ X => GoodCtrl t X m} (believe_me gy') gy' in
>   gy

> {-

> ---}
