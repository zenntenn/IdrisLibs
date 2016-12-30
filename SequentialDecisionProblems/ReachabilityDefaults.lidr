> module SequentialDecisionProblems.ReachabilityDefaults

> import SequentialDecisionProblems.CoreTheory

> import Sigma.Sigma

> %default total
> %auto_implicits off


This is the default implementation of |Reachable|: all states at the
first decision step are reachable; a state at decision step |t' = t + 1|
is reachable iff it has a reachable predecessor:

> SequentialDecisionProblems.CoreTheory.Reachable {t' = Z}   x' = Unit
> SequentialDecisionProblems.CoreTheory.Reachable {t' = S t} x' = Sigma (State t) (\ x => ReachablePred {t = t} x x')

If users can show that the monad |M| fulfills the specification

> allElemSpec1 : {A : Type} -> {P : A -> Type} ->
>                (ma : M A) -> ((a : A) -> a `Elem` ma -> P a) -> All P ma

we can easily shoe that if |x| is reachable and admits a control |y|,
then all states that can be obtained by selecting |y| in |x| are also
reachable, as required by the core theory:

> SequentialDecisionProblems.CoreTheory.reachableSpec1 {t} x r y = s where
>   f : (x' : State (S t)) -> x' `Elem` (nexts t x y) -> Reachable {t' = S t} x'
>   f x' x'en = MkSigma x (r, MkSigma y x'en)
>   s : All Reachable (nexts t x y)
>   s = allElemSpec1 (nexts t x y) f


> {-
 
> ---}
