> module EscardoOliva.Operations

> import Data.List

> import EscardoOliva.SelectionFunction
> import EscardoOliva.Quantifier

> %default total
> %access public export
> %auto_implicits off


> |||
> overline : {X, R : Type} -> J R X -> K R X
> overline e p = p (e p)


> |||
> otimes : {X : Type} -> {R : Type} ->
>          J R X -> (X -> J R (List X)) -> J R (List X)  
> otimes e f p = x :: xs where
>   x   =    e (\ x' => overline (f x') (\ xs' => p (x' :: xs')))
>   xs  =  f x (\ xs' => p (x :: xs'))


> |||
> partial
> bigotimes : {X, R : Type} -> List (List X -> J R X) -> J R (List X)
> bigotimes       []   =  \ p => []
> -- bigotimes (e :: es)  =  (e []) `otimes` (\x => bigotimes [\ xs => d (x :: xs) | d <- es])
> {-
> bigotimes {X} {R} (e :: es)  =  (e []) `otimes` f where
>   partial
>   f : X -> J R (List X)
>   f x = bigotimes (map h es) where
>     h : (List X -> J R X) -> List X -> J R X
>     h d = \ xs => d (x :: xs) 
> -}
> bigotimes {X} {R} (e :: es)  =  let f = \ x => bigotimes (map (\ d => \ xs => d (x :: xs) ) es) in
>                                 (e []) `otimes` f




> {-


> ---}
