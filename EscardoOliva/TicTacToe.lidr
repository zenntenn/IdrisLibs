> module Main

> import Data.List
> import Effects
> import Effect.Exception
> import Effect.StdIO

> import EscardoOliva.SelectionFunction
> import EscardoOliva.Quantifier
> import EscardoOliva.Operations

> %default total
> %access public export
> %auto_implicits off


> data Player =  X | O

> Outcome : Type
> Outcome = Int

> Move : Type
> Move = Int

> Board : Type
> Board = (List Move, List Move)

> contained : {X : Type} -> Ord X => List X -> List X -> Bool
> contained       []        ys  = True
> contained       xs        []  = False
> contained (x :: xs) (y :: ys) = if x == y 
>                                 then contained xs ys
>                                 else if x >= y
>                                      then contained (x :: xs) ys
>                                      else False

> someContained : {X : Type} -> Ord X => 
>                 List (List X) -> List X -> Bool
> someContained         []  ys  = False
> someContained        xss  []  = False
> someContained (xs :: xss) ys = contained xs ys || someContained xss ys

> wins : List Move -> Bool
> wins = someContained [[0,1,2],[3,4,5],[6,7,8],
>                       [0,3,6],[1,4,7],[2,5,8],
>                       [0,4,8],[2,4,6]]

> value : Board -> Outcome
> value (xs, os) = if wins xs 
>                  then 1
>                  else if wins os 
>                       then -1
>                       else 0

> insert : {X : Type} -> Ord X => X -> List X -> List X
> insert x [] = [x]
> insert x (y :: ys) = if x == y 
>                      then (y :: ys)
>                      else if x < y
>                           then x :: (y :: ys)
>                           else y :: (insert x ys) 

> outcome : Player -> List Move -> Board -> Board
> outcome _      Nil     board = board
> outcome X (m :: ms) (xs, os) = if wins os 
>                                then (xs, os)
>                                else outcome O ms (insert m xs, os)
> outcome O (m :: ms) (xs, os) = if wins xs 
>                                then (xs, os)
>                                else outcome X ms (xs, insert m os)

> delete : {X : Type} -> Ord X => X -> List X -> List X
> delete x [] = []
> delete x (y :: ys) = if x == y
>                      then ys
>                      else if x < y
>                           then y :: ys
>                           else y :: Main.delete x ys

> setMinus : {X : Type} -> Ord X => 
>            List X -> List X -> List X
> setMinus xs       []  = xs
> setMinus xs (y :: ys) = setMinus (Main.delete y xs) ys


> partial 
> epsilons : List (List Move -> J Outcome Move)
> epsilons = take 3 all where
>   partial
>   eX  :  List Move -> J Outcome Move
>   eX  =  \ h => argsup (setMinus [0..8] h)
>   partial
>   eO  :  List Move -> J Outcome Move
>   eO  =  \ h => arginf (setMinus [0..8] h)
>   partial
>   all :  List (List Move -> J Outcome Move)
>   all =  [eX, eO, eX, eO, eX, eO, eX, eO, eX, eO]

> p : List Move -> Outcome
> p ms = value (outcome X ms (Nil, Nil))

> partial
> optimalPlay : List Move
> optimalPlay = bigotimes epsilons p

> partial
> optimalOutcome : Outcome
> optimalOutcome = p optimalPlay

> partial
> main : IO ()
> main = 
>   do putStr ("An optimal play for Tic-Tac-Toe is "
>              ++
>              show optimalPlay ++ "\n"
>              ++
>              "and the optimal outcome is "
>              ++
>              show optimalOutcome ++ "\n"
>              )


> {-


> ---}


 
 
