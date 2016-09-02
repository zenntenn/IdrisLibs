> module Nat.Coprime


> import Nat.GCD
> import Nat.GCDAlgorithm
> import Unique.Predicates
> import Equality.Properties
> import Nat.GCDEuclid
> import Pairs.Operations
> import Sigma.Sigma


> %default total

> %access public export


> ||| 
> data Coprime : (m : Nat) -> (n : Nat) -> Type where
>   MkCoprime : {m, n : Nat} -> gcdAlg m n = S Z -> Coprime m n


> |||
> CoprimeUnique : {m, n : Nat} -> Unique (Coprime m n)
> CoprimeUnique {m} {n} (MkCoprime p) (MkCoprime q) = cong (uniqueEq (gcdAlg m n) (S Z) p q)
