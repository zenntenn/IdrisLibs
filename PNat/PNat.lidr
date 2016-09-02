> module PNat.PNat


> import Syntax.PreorderReasoning

> import Nat.Positive


> %default total
> %access public export


> ||| Positive natural numbers as sigma types
> PNat : Type
> PNat = Subset Nat Positive
