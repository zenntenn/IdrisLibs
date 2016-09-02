> module Nat.GCDEuclid


> import Nat.GCD
> import Nat.Divisor
> import Nat.DivisorProperties
> import Nat.Operations
> import Nat.LTEProperties
> import Nat.OperationsProperties
> import Sigma.Sigma
> import Pairs.Operations


> %default total
> %access public export
> %auto_implicits on


Euclid's greatest common divisor algorithm

> euclidGCD1 : GCD m m Z
> euclidGCD1 {m} = MkGCD (anyDivisorAny m) (anyDivisorZ m) (\ d' => \ d'Dm => \ d'DZ => d'Dm)

> euclidGCD2 : GCD m Z m
> euclidGCD2 {m} = MkGCD (anyDivisorZ m) (anyDivisorAny m) (\ d' => \ d'DZ => \ d'Dm => d'Dm)

> euclidGCD3 : m `LTE` n -> GCD d m (n - m) -> GCD d m n
> euclidGCD3 {m} {n} {d} p (MkGCD dDm dDnmm q) = MkGCD dDm dDn q' where
>   dDnmmpm : d `Divisor` ((n - m) + m)
>   dDnmmpm = divisorPlusLemma2 m (n - m) d dDm dDnmm
>   dDn : d `Divisor` n
>   dDn = replace {x = (n - m) + m}
>                 {y = n}
>                 {P = \ ZUZU => d `Divisor` ZUZU}
>                 (plusRightInverseMinus m n p)
>                 dDnmmpm
>   q' : (d' : Nat) -> d' `Divisor` m -> d' `Divisor` n -> d' `Divisor` d
>   q' d' d'Dm d'Dn = q d' d'Dm d'Dnmm where
>     d'Dnmm : d' `Divisor` (n - m)
>     d'Dnmm = divisorMinusLemma m n d' d'Dm d'Dn

> euclidGCD4 : Not (m `LTE` n) -> GCD d (m - n) n -> GCD d m n
> euclidGCD4 {m} {n} {d} p (MkGCD dDmmn dDn q) = MkGCD dDm dDn q' where
>   dDmmnpn : d `Divisor` ((m - n) + n)
>   dDmmnpn = divisorPlusLemma1 (m - n) n d dDmmn dDn
>   dDm : d `Divisor` m
>   dDm = replace {x = (m - n) + n}
>                 {y = m}
>                 {P = \ ZUZU => d `Divisor` ZUZU}
>                 (plusRightInverseMinus n m (notLTELemma1 m n p))
>                 dDmmnpn
>   q' : (d' : Nat) -> d' `Divisor` m -> d' `Divisor` n -> d' `Divisor` d
>   q' d' d'Dm d'Dn = q d' d'Dmmn d'Dn where
>     d'Dmmn : d' `Divisor` (m - n)
>     d'Dmmn = divisorMinusLemma n m d' d'Dn d'Dm

> euclidGCD : (m : Nat) -> (n : Nat) -> Sigma Nat (\ d => GCD d m n)
> euclidGCD    m   Z    = assert_total (MkSigma m euclidGCD1)
> euclidGCD  Z       n  = assert_total (MkSigma n euclidGCD2)
> euclidGCD (S m) (S n) with (decLTE (S m) (S n))
>   | (Yes p) = assert_total (MkSigma gcd (euclidGCD3 p P)) where
>     gcdP : Sigma Nat (\ d => GCD d (S m) (S n - S m))
>     gcdP = euclidGCD (S m) (S n - S m)
>     gcd  : Nat
>     gcd  = getWitness gcdP
>     P    : GCD gcd (S m) (S n - S m)
>     P    = getProof gcdP
>   | (No  p) = assert_total (MkSigma gcd (euclidGCD4 p P)) where
>     gcdP : Sigma Nat (\ d => GCD d (S m - S n) (S n))
>     gcdP = euclidGCD (S m - S n) (S n)
>     gcd  : Nat
>     gcd  = getWitness gcdP
>     P    : GCD gcd (S m - S n) (S n)
>     P    = getProof gcdP
