> module SequentialDecisionProblems.Generic.FullTheory

> import SequentialDecisionProblems.Generic.CoreAssumptions
> -- import SequentialDecisionProblems.Generic.ExtraAssumptions
> import SequentialDecisionProblems.Generic.CoreTheory

> import Sigma.Sigma
> import Sigma.Operations
> import Nat.OperationsProperties
> import Nat.Predicates
> import Nat.LTEProperties


> %default total
> %access public export
> %auto_implicits on


* The avoidability theory:

We can build a theory of avoidability on the top of the theory of
monadic SDPs. First we have to explain what it means for a possible
future state to be avoidable. For this, we have to introduce a
reachability relation:

> ReachableFrom : State t'' -> State t -> Type
> ReachableFrom  {t'' = Z   }  {t}  x''  x  =  (t = Z ,     x = x'')
> ReachableFrom  {t'' = S t'}  {t}  x''  x  =
>   Either  (t = S t' ,  x = x'') (Sigma (State t') (\ x' => (x' `ReachableFrom` x , x' `Pred` x'')))

It is easy to show that we are indeed modeling reachability of "future"
states:

> reachableFromLemma : (x'' : State t'') -> (x : State t) -> x'' `ReachableFrom` x -> t'' `GTE` t
> reachableFromLemma {t'' = Z}     {t = Z}     x'' x prf                   = LTEZero
> reachableFromLemma {t'' = S t'}  {t = Z}     x'' x prf                   = LTEZero
> reachableFromLemma {t'' = Z}     {t = S m}   x'' x (prf1 , prf2)         = void (uninhabited (sym prf1))
> reachableFromLemma {t'' = S t'}  {t = S t'}  x'' x (Left (Refl , prf2))  = eqInLTE (S t') (S t') Refl
> reachableFromLemma {t'' = S t'}  {t = t}     x'' x (Right (MkSigma x' (prf1 , prf2)))  = s2 where
>     s1  :  t' `GTE` t
>     s1  =  reachableFromLemma x' x prf1
>     s2  :  S t' `GTE` t
>     s2  =  idSuccPreservesLTE t t' s1

Now we can explain what it means for a state |x'| to be avoidable in a
decision process starting from a previous state |x|:

> Alternative : (x : State t) -> (m : Nat) -> (x' : State t') -> (x'' : State t') -> Type
> Alternative x m x' x'' = (x'' `ReachableFrom` x , Viable m x'' , Not (x'' = x'))

> AvoidableFrom'  :  (x' : State t') -> (x : State t) -> x' `ReachableFrom` x -> Viable n x' -> Type
> AvoidableFrom' {t'} {n} x' x r v = Exists (Alternative x n x')

> AvoidableFrom  :  (x' : State t') -> (x : State t) -> x' `ReachableFrom` x -> (m : Nat) -> Type
> AvoidableFrom {t'} x' x r m = Exists (Alternative x m x')


> {-


> ---}
