> module Opt.Operations


> import Control.Isomorphism
> import Data.Fin
> import Data.Vect
> import Syntax.PreorderReasoning

> import Finite.Predicates
> import Finite.Operations
> import Finite.Properties
> import Rel.TotalPreorder
> import Rel.TotalPreorderOperations
> import Vect.Operations
> import Vect.Properties
> import Fun.Operations
> import Nat.LTProperties


> %default total 

> %access public export


> argmaxMax : {A, B : Type} -> 
>             TotalPreorder B -> 
>             (fA : Finite A) -> 
>             (ne : CardNotZ fA) -> 
>             (f : A -> B) -> (A, B)
> argmaxMax {A} {B} tp fA nefA f = max (fromTotalPreorder2 tp) abs ltZn where
>   n    : Nat
>   n    = card fA
>   ltZn : LT Z n
>   ltZn = notZisgtZ nefA
>   abs  : Vect n (A,B)
>   abs  = map (pair (id, f)) (toVect fA)


> max : {A, B : Type} ->
>       TotalPreorder B -> 
>       (fA : Finite A) -> 
>       (ne : CardNotZ fA) -> 
>       (f : A -> B) -> B
> max tp fA nefA f = snd (argmaxMax tp fA nefA f)


> argmax : {A, B : Type} ->
>          TotalPreorder B -> 
>          (fA : Finite A) -> 
>          (ne : CardNotZ fA) -> 
>          (f : A -> B) -> A
> argmax tp fA nefA f = fst (argmaxMax tp fA nefA f)


> maxSpec : {A, B : Type} -> 
>           (tp : TotalPreorder B) -> 
>           (fA : Finite A) -> 
>           (nefA : CardNotZ fA) -> 
>           (f : A -> B) ->
>           (a : A) -> R tp (f a) (max tp fA nefA f)
> maxSpec {A} {B} tp fA nefA f a = s4 where
>   n    : Nat
>   n    = card fA
>   ltZn : LT Z n
>   ltZn = notZisgtZ nefA
>   abs  : Vect n (A,B)
>   abs  = map (pair (id, f)) (toVect fA)
>   s1   : Elem (a, f a) abs
>   s1   = mapLemma (toVect fA) (pair (id, f)) a (toVectComplete fA a)
>   s2   : (from2 (R tp)) (a, f a) (max (fromTotalPreorder2 tp) abs ltZn) 
>   s2   = maxLemma (fromTotalPreorder2 tp) (a, f a) abs ltZn s1
>   s3   : R tp (f a) (snd (max (fromTotalPreorder2 tp) abs ltZn))
>   s3   = s2
>   s4   : R tp (f a) (max tp fA nefA f)
>   s4   = s3


> argmaxSpec : {A, B : Type} -> 
>              (tp : TotalPreorder B) -> 
>              (fA : Finite A) -> 
>              (nefA : CardNotZ fA) -> 
>              (f : A -> B) ->
>              (max tp fA nefA f) = f (argmax tp fA nefA f)
> argmaxSpec {A} {B} tp fA nefA f = s3 where
>   ab : (A,B)
>   ab = argmaxMax tp fA nefA f
>   s1 : Elem ab (map (pair (Prelude.Basics.id, f)) (toVect fA))
>   s1 = maxElemLemma (fromTotalPreorder2 tp) (map (pair (id, f)) (toVect fA)) (notZisgtZ nefA)
>   s2 : f (fst ab) = snd ab
>   s2 = mapIdfLemma (toVect fA) f ab s1
>   s3 : max tp fA nefA f = f (argmax tp fA nefA f)
>   s3 = sym s2


> {-

> argmaxMax : {A, B : Type} -> {TO : B -> B -> Type} -> 
>             Preordered B TO => 
>             (fA : Finite A) -> (ne : CardNotZ fA) -> 
>             (f : A -> B) -> (A,B)
> argmaxMax {A} {B} {TO} fA nefA f = 
>   VectOperations.max {A = (A,B)} {TO = sndType TO} abs ltZn where
>     n    : Nat
>     n    = card fA
>     ltZn : LT Z n
>     ltZn = notZisgtZ nefA
>     abs  : Vect n (A,B)
>     abs  = map (pair (id, f)) (toVect fA)


> max : {A, B : Type} -> {TO : B -> B -> Type} -> 
>       Preordered B TO => 
>       (fA : Finite A) -> (ne : CardNotZ fA) -> 
>       (f : A -> B) -> B
> max fA nefA f = snd (argmaxMax fA nefA f)


> argmax : {A, B : Type} -> {TO : B -> B -> Type} -> 
>          Preordered B TO => 
>          (fA : Finite A) -> (ne : CardNotZ fA) -> 
>          (f : A -> B) -> A
> argmax fA nefA f = fst (argmaxMax fA nefA f)


> maxSpec : {A, B : Type} -> {TO : B -> B -> Type} -> 
>           Preordered B TO => 
>           (fA : Finite A) -> (nefA : CardNotZ fA) -> 
>           (f : A -> B) ->
>           (a : A) -> TO (f a) (max fA nefA f)
> maxSpec {A} {B} {TO} fA nefA f a = s4 where
>   n    : Nat
>   n    = card fA
>   ltZn : LT Z n
>   ltZn = notZisgtZ nefA
>   abs  : Vect n (A,B)
>   abs  = map (pair (id, f)) (toVect fA)
>   s1   : Elem (a, f a) abs
>   s1   = mapLemma (toVect fA) (pair (id, f)) a (toVectComplete fA a)
>   s2   : (sndType TO) (a, f a) (max abs ltZn) 
>   s2   = maxLemma (a, f a) abs ltZn s1
>   s3   : TO (f a) (snd (max abs ltZn))
>   s3   = s2
>   s4   : TO (f a) (max fA nefA f)
>   s4   = s3


> argmaxSpec : {A, B : Type} -> {TO : B -> B -> Type} -> 
>              Preordered B TO => 
>              (fA : Finite A) -> (nefA : CardNotZ fA) -> 
>              (f : A -> B) ->
>              (max fA nefA f) = f (argmax fA nefA f)
> argmaxSpec {A} {B} fA nefA f = s3 where
>   ab : (A,B)
>   ab = argmaxMax fA nefA f
>   s1 : Elem ab (map (pair (id, f)) (toVect fA))
>   s1 = maxElemLemma (map (pair (id, f)) (toVect fA)) (notZisgtZ nefA)
>   s2 : f (fst ab) = snd ab
>   s2 = mapIdfLemma (toVect fA) f ab s1
>   s3 : max fA nefA f = f (argmax fA nefA f)
>   s3 = sym s2

> -}
