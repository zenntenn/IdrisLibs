> module FunOperations


> %default total
> %access public export


> |||
> pair : (a -> b, a -> c) -> a -> (b, c)
> pair (f, g) x = (f x, g x)


> |||
> cross : (a -> c) -> (b -> d) -> (a, b) -> (c, d)
> cross f g (x, y) = (f x, g y)


> |||
> modifyFun : {a : Type} -> {b : Type} -> (Eq a) =>
>             (a -> b) -> a -> b -> (a -> b)
> modifyFun f a b a' = if a' == a then b else f a'
