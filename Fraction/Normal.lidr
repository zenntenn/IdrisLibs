> module Fraction.Normal


> import Fraction.Fraction
> import Fraction.BasicOperations
> import Nat.Coprime
> import Unique.Predicates
> import Nat.GCD
> import Nat.GCDEuclid
> import PNat.PNat
> import Nat.Positive
> import Pairs.Operations


> %default total

> %access public export


> ||| 
> data Normal : Fraction -> Type where
>   MkNormal  : {x : Fraction} -> Coprime (num x) (den x) -> Normal x

> |||
> NormalUnique : {x : Fraction} -> Unique (Normal x)
> NormalUnique {x} (MkNormal p) (MkNormal q) = cong (CoprimeUnique p q)

