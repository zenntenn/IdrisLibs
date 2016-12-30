> module Rel.Operations


> %default total
> %access public export


> |||
> pair : (a -> b -> Type, a -> c -> Type) -> a -> (b, c) -> Type
> pair (R, S) a (b, c) = (R a b, S a c)


> |||
> cross : (a -> c -> Type) -> (b -> d -> Type) -> (a, b) -> (c, d) -> Type
> cross R S (a, b) (c, d) = (R a c, S b d)

