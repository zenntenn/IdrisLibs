> module Main where


> type J r x = (x -> r) -> x

> type K r x = (x -> r) -> r


> overline :: J r x -> K r x
> overline e p = p (e p)


> otimes :: J r x -> (x -> J r [x]) -> J r [x]
> otimes e f p = x : xs where
>   x   =    e (\ x' -> overline (f x') (\ xs' -> p (x' : xs')))
>   xs  =  f x (\ xs' -> p (x : xs'))


> bigotimes ::  [[x] -> J r x] -> J r [x]
> bigotimes       []   =  \ p -> []
> bigotimes (e : es)   =  (e []) `otimes` (\x -> bigotimes [\ xs -> d (x : xs) | d <- es])


> argsup :: [x] -> J Int x
> argsup (x : []) p = x
> argsup (x : x' : xs) p = if p x < p x' then argsup (x' : xs) p else argsup (x : xs) p


> e :: [Int] -> J Int Int
> e _ = argsup [0..100]

> p :: [Int] -> Int
> p _ = 0


> main :: IO ()
> main = do putStr ("bigotimes (replicate 3 e) p = "
>                   ++
>                   show (bigotimes (replicate 3 e) p) ++ "\n")

> {-

> -}
