> module Nat.Divisor


> import Pairs.Operations


> %default total

> %access public export


> Divisor : (m : Nat) -> (n : Nat) -> Type
> Divisor m n = Subset Nat (\ q => m * q = n)

