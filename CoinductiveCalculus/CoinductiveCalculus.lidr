> module CoinductiveCalculus.CoinductiveCalculus


> %default total
> %access public export
> %auto_implicits on

> %hide Stream
> %hide head
> %hide tail
> %hide (::)

> Stream : Type -> Type

> head : Stream t -> t
> tail : Stream t -> Stream t
> (::) : t -> Stream t -> Stream t

> s1 : head (t :: s) = t  
> s2 : tail (t :: s) = s
> s3 : (head s) :: (tail s) = s 

We want to look at differentiation and integration of functions of real
variables in terms of streams. Let ...

> R : Type

...

> D : (R -> R) -> (R -> R)

> S : R -> R -> (R -> R) -> R


> StreamR : Type
> StreamR = R -> R

> headR : StreamR -> R
> headR f = f 0

