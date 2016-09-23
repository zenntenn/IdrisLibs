> module Sigma.Sigma

> %default total
> %access public export
> %auto_implicits on

> %hide Sigma
> %hide MkSigma


> data Sigma : (A : Type) -> (P : A -> Type) -> Type where
>   MkSigma : {A : Type} -> .{P : A -> Type} -> (x : A) -> (pf : P x) -> Sigma A P
