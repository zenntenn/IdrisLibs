> module Pair.Properties

> %default total
> %access public export
> %auto_implicits off


> pairLemma : {A, B : Type} -> (ab : (A, B)) -> ab = (fst ab, snd ab)
> pairLemma (a, b) = Refl

> pairEqElimFst : {A, B : Type} -> {a, a' : A} -> {b, b' : B} -> (a, b) = (a', b') -> a = a' 
> pairEqElimFst Refl = Refl

> pairEqElimSnd : {A, B : Type} -> {a, a' : A} -> {b, b' : B} -> (a, b) = (a', b') -> b = b' 
> pairEqElimSnd Refl = Refl
