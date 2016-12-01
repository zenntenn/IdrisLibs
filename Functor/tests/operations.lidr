> module Functor.tests.Main

> import Control.Monad.Identity

> import Functor.Operations
> import Identity.Properties

> %default total
> %auto_implicits off

> b : Bool
> b = elem Z (Id Z)

> B : Type
> B = Elem Z (Id Z)

> b' : Bool
> b' = decAsBool (decElem Z (Id Z))

> main : IO ()
> main = do putStrLn ("b  = " ++ show b)
>           putStrLn ("b' = " ++ show b')




