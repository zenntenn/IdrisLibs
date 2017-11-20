> module papers.JFP2016.Deterministic

> import Sigma.Sigma

> %default total
> %access public export
> %auto_implicits on


* Sequential decision processes

> State : (t : Nat) -> Type

> Ctrl : (t : Nat) -> (x : State t) -> Type

> next : (t : Nat) -> (x : State t) -> (y : Ctrl t x) -> State (S t)


* Sequential decision problems

> Val : Type

> reward  : (t : Nat) -> (x : State t) -> (y : Ctrl t x) -> (x' : State (S t)) -> Val

> plus : Val -> Val -> Val

> zero : Val

> LTE : Val -> Val -> Type


* Viability

> Viable  :  (n : Nat) -> State t -> Type

> Good            :  (t : Nat) -> (x : State t) -> (n : Nat) -> (Ctrl t x) -> Type
> Good t x n y    =  Viable {t = S t} n (next t x y)

> GoodCtrl        :  (t : Nat) -> (x : State t) -> (n : Nat) -> Type
> GoodCtrl t x n  =  Sigma (Ctrl t x) (Good t x n)

> viableSpec0  :  (x : State t) -> Viable Z x
> viableSpec1  :  (x : State t) -> Viable (S n) x -> GoodCtrl t x n
> viableSpec2  :  (x : State t) -> GoodCtrl t x n -> Viable (S n) x


* Reachability

> Reachable       :  State t' -> Type

> Pred                :  State t -> State (S t) -> Type
> Pred {t} x x'       =  Sigma (Ctrl t x) (\ y => x' = next t x y)
>
> ReachablePred       :  State t -> State (S t) -> Type
> ReachablePred x x'  =  (Reachable x, x `Pred` x')


> reachableSpec0  :  (x : State Z) -> Reachable x
> reachableSpec1  :  (x : State t) -> Reachable x -> (y : Ctrl t x) -> Reachable (next t x y)
> reachableSpec2  :  (x' : State (S t)) -> Reachable x' -> Sigma (State t) (\ x => x `ReachablePred` x')


* Policies and policy sequences

> Policy : (t : Nat) -> (n : Nat) -> Type
> Policy t Z      =  Unit
> -- Policy t (S m)  =  (x : State t) -> Viable (S m) x -> GoodCtrl t x m
> Policy t (S m)  =  (x : State t) -> Reachable x -> Viable (S m) x -> GoodCtrl t x m

> data PolicySeq : (t : Nat) -> (n : Nat) -> Type where
>   Nil   :  PolicySeq t Z
>   (::)  :  Policy t (S n) -> PolicySeq (S t) n -> PolicySeq t (S n)
