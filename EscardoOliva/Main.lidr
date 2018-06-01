> module Main

> %default total
> %access public export
> %auto_implicits off

> J : Type -> Type -> Type
> J R X = (X -> R) -> X

> K : Type -> Type -> Type
> K R X = (X -> R) -> R

> overline : {X, R : Type} -> J R X -> K R X
> overline e p = p (e p)

> otimes : {X, R : Type} -> J R X -> (X -> J R (List X)) -> J R (List X)  
> otimes e f p = x :: xs where
>   x   =    e (\ x' => overline (f x') (\ xs' => p (x' :: xs')))
>   xs  =  f x (\ xs' => p (x :: xs'))

> partial
> bigotimes : {X, R : Type} -> List (List X -> J R X) -> J R (List X)
> bigotimes       []   =  \ p => []
> bigotimes (e :: es)  =  (e []) `otimes` (\x => bigotimes [\ xs => d (x :: xs) | d <- es])

> partial
> argsup : {X : Type} -> (xs : List X) -> J Int X
> argsup (x :: Nil) p = x
> argsup (x :: x' :: xs) p = if p x < p x' then argsup (x' :: xs) p else argsup (x :: xs) p

> partial
> e : List Int -> J Int Int
> e _ = argsup [0..2]

> p : List Int -> Int
> p _ = 0

> partial
> main : IO ()
> main = do putStr ("bigotimes (replicate 3 e) p = "
>                   ++
>                   show (bigotimes (replicate 3 e) p) ++ "\n")

