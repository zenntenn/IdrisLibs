> module SimpleProb.Functor

> import SimpleProb.SimpleProb
> import SimpleProb.MonadicOperations

> %default total
> %access public export
> %auto_implicits on


> ||| |SimpleProb| is a functor:
> implementation Functor SimpleProb where
>   map = fmap


> {-

> ---}
