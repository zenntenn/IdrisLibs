> module papers.JFP2016.Stochastic

> import Sigma.Sigma
> import SimpleProb.SimpleProb

> %default total
> %access public export
> %auto_implicits off


> State : (t : Nat) -> Type

> Ctrl : (t : Nat) -> (x : State t) -> Type

> nexts : (t : Nat) -> (x : State t) -> (y : Ctrl t x) -> SimpleProb (State (S t))

> fmap  :  {A, B : Type} -> 
>          (A -> B) -> SimpleProb A -> SimpleProb B
> postulate functorSpec1  :  fmap . id = id
> postulate functorSpec2  :  {A, B, C : Type} -> {f : B -> C} -> {g : A -> B} ->
>                            fmap (f . g) = (fmap f) . (fmap g)

> Val : Type

> reward : (t : Nat) -> (x : State t) -> (y : Ctrl t x) -> (x' : State (S t)) -> Val

> rewards  : (t : Nat) -> (x : State t) -> (y : Ctrl t x) -> SimpleProb Val
> rewards t x y = fmap (reward t x y) (nexts t x y)

> {-

> ---}
