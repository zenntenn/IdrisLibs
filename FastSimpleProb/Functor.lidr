> module FastSimpleProb.Functor

> import FastSimpleProb.SimpleProb
> import FastSimpleProb.MonadicOperations

> %default total
> %access public export
> %auto_implicits on


> ||| |SimpleProb| is a functor:
> implementation Functor SimpleProb where
>   map = fmap


> {-

> ---}
