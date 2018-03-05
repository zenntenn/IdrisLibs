> module Main

> import Data.Fin
> import Data.Vect
> import Data.Matrix
> import Data.Matrix.Numeric

> %default total
> %access public export
> %auto_implicits off


* Preliminaries

This is a re-implementation of

  https://gist.github.com/mrkgnao/a45059869590d59f05100f4120595623 

which, in turn, is an Idris implementation of

  https://blog.jle.im/entry/practical-dependent-types-in-haskell-1.html


* Layers

A layer of type |X| with |m| inputs and |n| outputs is a tuple
consisting of a function of type |A -> A|, its first derivative, a
vector of |n| elements of type |X| (the biases) and a |n| x |m| matrix
of elements of type |X| (the weights):

> Layer : (X : Type) -> (m : Nat) -> (n : Nat) -> Type
> Layer X m n = (X -> X, X -> X, Vect n X, Matrix n m X)


* Sequential neural networks

A sequential neural network of type |X| with |m| inputs, |n| outputs and
a sequence of intermediate layers is a sequence of layers of type
|X|. It can consist of either a single layer or of a layer with |m|
inputs and |m'| outputs together with a network with |m'| inputs and |n|
outputs:

> infixr 5 :>:

> data Network : (A : Type) -> List Nat -> (n : Nat) -> Type where
>   Single :  {X : Type} -> {m, n : Nat} -> 
>             Layer X m n -> Network X [m] n
>   (:>:)  :  {X : Type} -> {m, m', n : Nat} -> {ms : List Nat} -> 
>             Layer X m m' -> Network X (m' :: ms) n -> Network X (m :: m' :: ms) n



* Feed-forward

The idea is that, given a sequential neural network of type |X| with |m|
inputs and |n| outputs and a vector of |m| inputs of matching type, one
can compute a vector of |n| outputs. The computation is called
feed-forward.

> feedForward : {X : Type} -> {m, n : Nat} -> {ms : List Nat} -> 
>               Num X => 
>               Network X (m :: ms) n -> Vect m X -> Vect n X

The idea is to feed the input into the first layer and pass its outputas
input for the next layers. With

> evalLayer : {X : Type} -> {m, n : Nat} -> 
>             Num X => 
>             Layer X m n -> Vect m X -> Vect n X
> evalLayer (s, s', b, w) x = map s (b + (w </> x))

the implementation of |feedForward| is trivial:

> feedForward (Single l) x = evalLayer l x
> feedForward (l :>: ls) x = feedForward ls (evalLayer l x)


* Error

Given a training pair |(x, y)|, the error is simply the difference
between |y| and the output of the network when fed with the input |x|:

> error : {X : Type} -> {n, m : Nat} -> {ms : List Nat} -> Num X => Neg X =>
>         Network X (m :: ms) n -> Vect m X -> Vect n X -> Vect n X
> error net x y = y - (feedForward net x)


* Back propagation

> backPropagation : {X : Type} -> {n, m : Nat} -> {ms : List Nat} -> 
>                   Num X => Neg X =>
>                   (eta : X) ->
>                   (x   : Vect m X) ->
>                   (y   : Vect n X) ->
>                   Network X (m :: ms) n -> 
>                   Network X (m :: ms) n

> backPropagation {X} eta x y net = fst (go x y net)
> 
>   where go : {m, n : Nat} -> {ms : List Nat} ->
>              Vect m X -> 
>              Vect n X ->  
>              Network X (m :: ms) n -> (Network X (m :: ms) n, Vect m X)
>   
>         go x y (Single (s, s', b, w)) =
>           let z    = b + (w </> x)
>               x'   = map s z
>               dEdy = (map s' z) * (x' - y)
>               b'   = b - (eta <# dEdy)
>               w'   = w - (eta <#> (dEdy >< x))
>               dWs  = (transpose w) </> dEdy
>           in (Single (s, s', b', w'), dWs)
>           
>         go x y ((s, s', b, w) :>: ls) =
>           let z           = b + (w </> x)
>               x'          = map s z
>               (ls', dWs') = go x' y ls
>               dEdy        = (map s' z) * dWs'
>               b'          = b - (eta <# dEdy)
>               w'          = w - (eta <#> (dEdy >< x))
>               dWs         = (transpose w) </> dEdy
>           in ((s, s', b', w') :>: ls', dWs)


* Example

> s : Double -> Double
> s x = 1 / (1 + exp (-x))

> s' : Double -> Double
> s' x = (s x) * (1 - s x)

> initial : Network Double [2,2] 2 
> initial = (s, s', [0.35, 0.35], [[0.15, 0.20], [0.25, 0.30]])
>           :>:
>           Single (s, s', [0.60, 0.60], [[0.40, 0.45], [0.50, 0.55]])

> input : Vect 2 Double
> input = [0.05, 0.10]

> target : Vect 2 Double
> target = [0.01, 0.99]

> main : IO ()
> main = let step   = backPropagation 0.5 input target
>            errorF = \ net => error net input target
>            states = iterate step initial
>        in putStrLn . unlines $ map (show . errorF) (take 100 states)


> {-

> ---}






