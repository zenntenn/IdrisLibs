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

A layer of type |A| with |n| inputs and |m| outputs is a vector of |m|
elements of type |A| (the biases) and a |m| x |n| matrix of elements of
type |A| (the weights):

> data Layer : Nat -> Nat -> Type -> Type where
>   MkLayer : {m, n : Nat} -> {A : Type} -> 
>             (biases : Vect m A) -> (weights : Matrix m n A) -> Layer n m A


* Sequential neural networks

A sequential neural network of type |A| with |n| inputs, |m| outputs and
a sequence of intermediate layers is a sequence of layers of type
|A|. It can consist of either a single (Output) layer or of a layer with
|n| inputs and |k| outputs together with a network with |k| inputs and
|m| outputs:

> infixr 5 :>:

> data Network : Nat -> List Nat -> Nat -> Type -> Type where
>   Output : {n, m : Nat} -> {A : Type} -> 
>            Layer n m A -> Network n [] m A
>   (:>:)  : {n, k, m : Nat} -> {ks : List Nat} -> {A : Type} -> 
>            Layer n k A -> Network k ks m A -> Network n (k :: ks) m A



* Feed-forward

The idea is that, given a sequential neural network of type |A| with |n|
inputs and |m| outputs and a vector of |n| inputs of matching type, one
can compute a vector of |n| outputs.

The computation is called feed-forward. It requires |A| to implement
addition and multiplication and depends on an "activation" function |s :
A -> A|:

> feedForward : {n, m : Nat} -> {ks : List Nat} -> {A : Type} -> Num A => 
>               (A -> A) -> Vect n A -> Network n ks m A -> Vect m A

The idea is to feed the input into the first layer and pass its output
(activated through |s|) as input for the next layer. With

> evalLayer : {n, m : Nat} -> {t : Type} -> Num t => 
>             Vect n t -> Layer n m t -> Vect m t
> evalLayer {n} {m} {t} input (MkLayer biases weights) = output where
>   output : Vect m t
>   output = biases + (weights </> input)

the implementation of |feedForward| is trivial:

> feedForward s input (Output l) = map s (evalLayer input l)
> feedForward s input (l :>: ls) = feedForward s (map s (evalLayer input l)) ls


* Error

Given a training pair |(x, y)|, the error is simply the difference
between |y| and the output of the network when fed with the input |x|:

> error : {n, m : Nat} -> {ks : List Nat} -> {t : Type} -> Num t => Neg t =>
>         (t -> t) -> Vect n t -> Vect m t -> Network n ks m t -> Vect m t
> error {m} {t} s input target network = target - output where
>   output : Vect m t
>   output = (feedForward s input network)


* Back propagation

> backPropagation : {n, m : Nat} -> {ks : List Nat} -> {t : Type} -> 
>                   Num t => Neg t =>
>                   (s      : t -> t) ->
>                   (s'     : t -> t) ->
>                   (eta    : t) ->
>                   (input  : Vect n t) ->
>                   (target : Vect m t) ->
>                   Network n ks m t -> Network n ks m t

> backPropagation {t} s s' eta input target net = fst (go input target net)
> 
>   where go : {n, m : Nat} -> {ks : List Nat} ->
>              Vect n t -> Vect m t ->  Network n ks m t -> (Network n ks m t, Vect n t)
>   
>         go input target ((MkLayer bias weights) :>: rest) =
>           let y             = evalLayer input (MkLayer bias weights)
>               output        = map s y
>               (rest', dWs') = go output target rest
>               dEdy          = (map s' y) * dWs'
>               bias'         = bias - (eta <# dEdy)
>               weights'      = weights - (eta <#> (dEdy >< input))
>               layer'        = (MkLayer bias' weights')
>               dWs           = (transpose weights) </> dEdy
>           in (layer' :>: rest', dWs)
>
>         go input target (Output (MkLayer bias weights)) =
>           let y        = evalLayer input (MkLayer bias weights)
>               output   = map s y
>               dEdy     = (map s' y) * (output - target)
>               bias'    = bias - (eta <# dEdy)
>               weights' = weights - (eta <#> (dEdy >< input))
>               layer'   = (MkLayer bias' weights')
>               dWs      = (transpose weights) </> dEdy
>           in (Output layer', dWs)


* Example

> initial : Network 2 [2] 2 Double
> initial = first :>: second
>   where first  = MkLayer [0.35, 0.35]
>                          [ [0.15, 0.20],
>                            [0.25, 0.30]
>                          ]
>         second = Output
>                $ MkLayer [0.60, 0.60]
>                          [ [0.40, 0.45],
>                            [0.50, 0.55]
>                          ]

> input : Vect 2 Double
> input = [0.05,0.10]

> target : Vect 2 Double
> target = [0.01,0.99]

> s : Double -> Double
> s x = 1 / (1 + exp (-x))

> s' : Double -> Double
> s' x = (s x) * (1 - s x)

> main : IO ()
> main = let step   = backPropagation s s' 0.5 input target
>            errorF = error s input target
>            states = iterate step initial
>        in putStrLn . unlines $ map (show . errorF) (take 100 states)


> {-

> ---}

