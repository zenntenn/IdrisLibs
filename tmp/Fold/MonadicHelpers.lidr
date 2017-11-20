> module papers.JFP2016.MonadicHelpers

> import Data.Fin
> import Control.Isomorphism

> import papers.JFP2016.MonadicCore
> import Finite.Predicates
> import Finite.Operations
> import Finite.Properties
> import Sigma.Sigma
> import Sigma.Operations
> import Sigma.Properties

> %default total
> %access public export
> %auto_implicits off


* Finiteness notions

> |||
> FiniteViable : Type
> FiniteViable = {t : Nat} -> 
>                (n : Nat) -> (x : State t) -> Finite (Viable {t} n x)

> |||
> FiniteAll : Type
> FiniteAll = {A : Type} -> {P : A -> Type} -> 
>             Finite1 P -> (ma : M A) -> Finite (All P ma)

> |||
> FiniteAllViable : Type
> FiniteAllViable = {t : Nat} -> {n : Nat} -> 
>                   (x : State t) -> (y : Ctrl t x) -> 
>                   Finite (All (Viable {t = S t} n) (nexts t x y))

> |||
> FiniteNotEmpty : Type
> FiniteNotEmpty = {t : Nat} -> {n : Nat} -> 
>                  (x : State t) -> (y : Ctrl t x) -> 
>                  Finite (NotEmpty (nexts t x y))

> |||
> FiniteGood : Type
> FiniteGood = {t : Nat} -> {n : Nat} -> 
>              (x : State t) -> (y : Ctrl t x) -> 
>              Finite (Good t x n y)

> |||
> FiniteCtrl : Type
> FiniteCtrl = {t : Nat} -> {n : Nat} -> 
>              (x : State t) -> Finite (Ctrl t x) 

> |||
> FiniteGoodCtrl : Type
> FiniteGoodCtrl = {t : Nat} -> {n : Nat} -> 
>                  (x : State t) -> Viable {t = t} (S n) x ->
>                  Finite (GoodCtrl t x n) 


* Standard deduction patterns in the implementation of specific SDPs

> finiteAll : {A : Type} -> {P : A -> Type} -> 
>             Finite1 P -> (ma : M A) -> Finite (All P ma)

> finiteViable : {t : Nat} -> {n : Nat} -> 
>                (x : State t) -> Finite (Viable {t} n x)

> finiteAllViable : {t : Nat} -> {n : Nat} -> 
>                   (x : State t) -> (y : Ctrl t x) -> 
>                   Finite (All (Viable {t = S t} n) (nexts t x y))
> finiteAllViable {t} {n} x y = finiteAll (finiteViable {t = S t} {n}) (nexts t x y)

> finiteNotEmpty : {t : Nat} -> {n : Nat} -> 
>                  (x : State t) -> (y : Ctrl t x) -> 
>                  Finite (NotEmpty (nexts t x y))

> finiteGood : {t : Nat} -> {n : Nat} -> 
>              (x : State t) -> (y : Ctrl t x) -> 
>              Finite (Good t x n y)
> finiteGood {n} x y = finiteProduct (finiteNotEmpty {n} x y) (finiteAllViable x y)

> finiteCtrl : {t : Nat} -> {n : Nat} -> (x : State t) -> Finite (Ctrl t x) 

> finiteGoodCtrl : {t : Nat} -> {n : Nat} -> 
>                  (x : State t) -> 
>                  Finite (GoodCtrl t x n) 
> finiteGoodCtrl {t} {n} x = finiteSigmaLemma0 (finiteCtrl {t} {n} x) (finiteGood {t} {n} x)

> cardNotZGoodCtrl : {t : Nat} -> {n : Nat} -> 
>                    (x : State t) -> (v : Viable {t = t} (S n) x) ->
>                    CardNotZ (finiteGoodCtrl {t} {n} x)
> cardNotZGoodCtrl x v = cardNotZLemma (finiteGoodCtrl x) (viableSpec1 x v)


> {-
 
> ---}
 
