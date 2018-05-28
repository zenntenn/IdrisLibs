> module Main

> import Data.List

> import EscardoOliva.SelectionFunction
> import EscardoOliva.Operations

> %default total
> %access public export
> %auto_implicits off

> xs : List Int
> xs = [7,-3]

> partial 
> e : J Int Int
> e = argsup xs 

> f : Int -> J Int (List Int)
> f i = \ p => [p [i, i, i]]

> partial 
> es : J Int (List Int)
> es = otimes e f

> partial
> ys : List Int
> ys = es sum

> partial
> main : IO ()
> main = do putStr ("ys = " ++ show ys ++ "\n")

> {-

> ---}
