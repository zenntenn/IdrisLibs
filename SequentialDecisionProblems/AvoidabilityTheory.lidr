> module SequentialDecisionProblems.FullTheory

> import SequentialDecisionProblems.CoreTheory

> import Sigma.Sigma
> import Sigma.Operations
> import Nat.OperationsProperties
> import Nat.Predicates
> import Nat.LTEProperties
> import Finite.Predicates
> import Finite.Properties
> import Decidable.Predicates
> import Decidable.Properties

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
> AvoidableFrom' {t'} {n} x' x r v = Sigma (State t') (\ x'' => Alternative x n x' x'')

> AvoidableFrom  :  (x' : State t') -> (x : State t) -> x' `ReachableFrom` x -> (m : Nat) -> Type
> AvoidableFrom {t'} x' x r m = Sigma (State t') (\ x'' => Alternative x m x' x'')


* Decidability of |Viable|

A relevant question for applications is under which conditions
avoidability is decidable. A fundamental result is that, for a finite
type |A| and a decidable predicate |P : A -> Type|, |Sigma A P| is
decidable, see

< finiteDecSigmaLemma : {A : Type} -> {P : A -> Type} -> Finite A -> Dec1 P -> Dec (Sigma A P)

in |Finite.Properties|. 

> decEqState : (x : State t) -> (x' : State t') -> Dec (x = x')

> SequentialDecisionProblems.CoreTheory.Viable {t}  Z     _  =  Unit
> SequentialDecisionProblems.CoreTheory.Viable {t} (S m)  x  =  GoodCtrl t x m

> SequentialDecisionProblems.CoreTheory.viableSpec0 _ = ()
> SequentialDecisionProblems.CoreTheory.viableSpec1 x = id
> SequentialDecisionProblems.CoreTheory.viableSpec2 x = id

> finCtrl      :  (x : State t) -> Finite (Ctrl t x)
> -- decAll       :  {A : Type} -> (P : A -> Type) -> ((a : A) -> Dec (P a)) -> (ma : M A) -> Dec (All P ma)
> -- decNotEmpty  :  {A : Type} -> (ma : M A) -> Dec (NotEmpty ma)
> decAll       :  (P : (State t) -> Type) -> ((x : State t) -> Dec (P x)) -> (mx : M (State t)) -> Dec (All P mx)
> decNotEmpty  :  (mx : M (State t)) -> Dec (NotEmpty mx)

> mutual

>   decGood  :  (x : State t) ->  (m : Nat) -> (y : Ctrl t x) -> Dec (Good t x m y)
>   decGood {t} x m y = decPair (decNotEmpty mx') (decAll (Viable m) (decViable m) mx') where
>     mx' : M (State (S t))
>     mx' = nexts t x y

>   decViable : (n : Nat) -> (x : State t) -> Dec (Viable n x)
>   decViable      Z    _ = Yes ()
>   decViable {t} (S m) x = finiteDecSigmaLemma (finCtrl x) (decGood x m)


* Decidability of |ReachableFrom|

> -- decElem : {A : Type} -> (a : A) -> (ma : M A) -> Dec (a `Elem` ma)
> decElem : (x : State t) -> (mx : M (State t)) -> Dec (x `Elem` mx) 

> decPred : (x : State t) -> (x' : State (S t)) -> Dec (x `Pred` x')
> decPred {t} x x' = finiteDecSigmaLemma (finCtrl x) (\ y => decElem x' (nexts t x y))

> finState :  (t : Nat) -> Finite (State t)

> decReachableFrom : (x'' : State t'') -> (x : State t) -> Dec (x'' `ReachableFrom` x)
> decReachableFrom {t'' = Z   } {t} x'' x = decPair dp dq where
>   dp : Dec (t = Z)
>   dp = decEq t Z
>   dq : Dec (x = x'')
>   dq = decEqState x x''
> decReachableFrom {t'' = S t'} {t} x'' x = decEither dp dq where
>   dp : Dec (t = S t' , x = x'')
>   dp = decPair (decEq t (S t')) (decEqState x x'')
>   dq : Dec (Sigma (State t') (\ x' => (x' `ReachableFrom` x , x' `Pred` x'')))
>   dq = finiteDecSigmaLemma fState dRP where
>     fState  :  Finite (State t')
>     fState  =  finState t'
>     -- dRP : Dec1 (\ x' => (x' `ReachableFrom` x , x' `Pred` x''))
>     dRP : (x' : State t') -> Dec (x' `ReachableFrom` x , x' `Pred` x'')
>     dRP x' = decPair drf dpred where
>       drf    :  Dec (x' `ReachableFrom` x)
>       drf    =  decReachableFrom x' x
>       dpred  :  Dec (x' `Pred` x'')
>       dpred  =  decPred x' x''




> {-


> ---}
