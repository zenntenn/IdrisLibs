> module Nat.GCD


> import Nat.Divisor


> %default total
> %access public export
> %auto_implicits on


> |||
> data GCD : (d : Nat) -> (m : Nat) -> (n : Nat) -> Type where
>   MkGCD : d `Divisor` m ->
>           d `Divisor` n ->
>           ((d' : Nat) -> d' `Divisor` m -> d' `Divisor` n -> d' `Divisor` d) ->
>           GCD d m n

