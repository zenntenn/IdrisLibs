> module papers.JFP2016.Deterministic

> %default total
> %access public export
> %auto_implicits on


> State : (t : Nat) -> Type

> Ctrl : (t : Nat) -> (x : State t) -> Type

> next : (t : Nat) -> (x : State t) -> (y : Ctrl t x) -> State (S t)

> Val : Type

> reward  : (t : Nat) -> (x : State t) -> (y : Ctrl t x) -> (x' : State (S t)) -> Val

