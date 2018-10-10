> module Equality.Properties


> import Unique.Predicates


> %default total

> %access public export


> ||| If |P| and |Q| are equality decidable, |(P , Q)| is equality decidable
> decPair : {P, Q : Type} -> DecEq P -> DecEq Q -> DecEq (P , Q)
> decPair {P} {Q} dp dq = %implementation
> {-
> decPair {P} {Q} dp dq = d where
>   implementation [d] DecEq (P, Q) where
>     decEq _ _ = ?kiku
> -}

> ||| Equality is unique
> uniqueEq : {A : Type} -> (a1 : A) -> (a2 : A) -> Unique (a1 = a2)
> uniqueEq a a Refl Refl = Refl
> %freeze uniqueEq -- frozen

