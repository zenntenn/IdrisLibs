> module EscardoOliva.SelectionFunction

> %default total
> %access public export
> %auto_implicits off


> ||| Selection function
> J : Type -> Type -> Type
> J R X = (X -> R) -> X


* Selection functions for quantifiers

> ||| 
> partial
> argsup : {X : Type} -> (xs : List X) -> J Int X
> argsup (x :: Nil) p = x
> argsup (x :: x' :: xs) p = if p x < p x' then argsup (x' :: xs) p else argsup (x :: xs) p

> |||
> partial
> arginf : {X : Type} -> (xs : List X) -> J Int X
> arginf xs p = argsup xs (\ x => - p x)


