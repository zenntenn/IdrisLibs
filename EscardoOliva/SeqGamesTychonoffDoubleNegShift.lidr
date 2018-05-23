> module SeqGamesTychonoffDoubleNegShift

> import Syntax.PreorderReasoning
> import Data.List

> %default total
> %access public export
> %auto_implicits off

* Section 1

They start from the offset with |bigotimes|, the function to be
discussed in the paper

> bigotimes : {X, R : Type} -> List ((X -> R) -> X) -> (List X -> R) -> List X
> bigotimes  Nil      p = Nil
> bigotimes (e :: es) p = x0 :: bigotimes es (p . (x0 ::)) where
>   x0 = e (\ x => p (x :: bigotimes es (p . (x ::))))

, introduce the notion of selection function

> Selection : Type -> Type -> Type 
> Selection X R = (X -> R) -> X

and of a "binary operation that combines two selection functions" in
terms of which |bigotimes| can be implemented recursively. In the rest
of the section they relate |bigotimes| with sequential games (apparently
deterministic, with finite or infinite number of steps and alternating
players), with the Tychonoff theorem and with the Double-Negation Shift
(DNS). Then they present an outline of the paper.


* Section 2

They start by introducing shortcuts for (flipped) selection functions

> J : Type -> Type -> Type
> J R X = (X -> R) -> X

and generalized quantifiers 

> K : Type -> Type -> Type
> K R X = (X -> R) -> R

Here, |R| represents generalized truth values. The text suggests that
selection functions of type |J R X| and quantifiers of type |K R X| take
as arguments functions of type |X -> R| that represent properties of
values of type |X|, see the "Terminology" table.

As a matter of fact, however, these functions are not dependently
typed. I think that the arguments of selection functions and quantifiers
are in fact decision procedured associated for a decidable property of
interest. Thus, for instance, for |X = Nat| and |R = Bool|, one could
have

> P : Nat -> Type
> P i = LTE i 42

and

> dP : Nat -> Bool
> dP i = if i <= 42 then True else False

Anyway, the authors go on by remarking that, with the |J| operator, the
type of |bigotimes| can be rewritten as

< bigotimes : {X, R : Type} -> List (J R X) -> J R (List X)

They then introduce

> overline : {X, R : Type} -> J R X -> K R X
> overline e = \ p => p (e p)

and start discussing selection functions for sets in a subsection. 


** Section 2.1 

Escardo-Oliva start by stating that "A selection function for a set S
finds an element of S for which a given predicate holds". They require
selection functions for sets to be total and point out that "if there is
no element of S satisfying the predicate, we select an arbitrary element
of S". Thus, selection functions for sets are only defined for non-empty
sets

> find : {X : Type} -> (xs : List X) -> NonEmpty xs -> J Bool X
> find      Nil  _ p impossible
> find (x :: xs) _ p with (nonEmpty xs)
>   | (Yes prf) = if p x then x else find xs prf p
>   | ( No prf) = x

> forsome : {X : Type} -> (xs : List X) -> NonEmpty xs -> K Bool X
> forsome xs ne = overline (find xs ne)

> forevery : {X : Type} -> (xs : List X) -> NonEmpty xs -> K Bool X
> forevery xs ne p = not (forsome xs ne (not . p))

At this point, Escardo-Oliva point out that their definition of the
existential quantifier is the same as in Hilbert’s ε-calculus: 

  ∃x p(x) ⇐⇒ p(ε(p)).

This looks like a claim about |find|:

> findLemma1 : {X : Type} -> 
>              (xs : List X) -> (ne : NonEmpty xs) -> (p : X -> Bool) -> 
>              (x ** p x = True) -> p (find xs ne p) = True

> findLemma2 : {X : Type} -> 
>              (xs : List X) -> (ne : NonEmpty xs) -> (p : X -> Bool) -> 
>              p (find xs ne p) = True -> (x ** p x = True)

The second lemma holds trivially

> findLemma2 {X} xs ne p prf = (find xs ne p ** prf) 

and it should not be difficult to show that the first one holds as well
using the implementation of |find|:

> findLemma2 {X}      Nil  _ p prf impossible
> findLemma2 {X} (x :: xs) _ p prf = ?lala

Further, they state that a selection function ε for a set S has to
satisfy:

1. ε(p) ∈ S, whether or not there actually is some x ∈ S such that p(x)
   holds.

2. If p(x) holds for some x ∈ S, then it holds for x = ε(p).

With the helper function

> typeOf : {X : Type} -> X -> Type
> typeOf {X} _ = X 

the first condition boils down to

> SpecJ1 : {X, R : Type} -> (eps : J R X) -> (p : X -> R) -> typeOf (eps p) = X

which trivially holds

> SpecJ1 eps p = Refl

In the second condition it is not completely clear what it means for
p(x) to "hold". If we restrict ourselves to the case in which |R =
Bool|, I think that the condition could be written as

< SpecJ2 : {X : Type} -> (eps : J Bool X) -> (p : X -> Bool) -> (x : X) -> p x = True -> p (eps p) = True  

Here we have translated "p(x) holds" with |p x = True|. If the arguments
of selection functions and quantifiers were truly propositions, we would
again know how to formalize condition 2

< SpecJ2 : {X : Type} -> (eps : J Type X) -> (p : X -> Type) -> (x : X) -> p x -> p (eps p)


** Section 2.2

Hilbert's condition

  ϕ p = p (ε p)

is used to express what it means for a selection function to be
compatible with a quantifier:

> infixl 9 <> 

> (<>) : {X, R : Type} -> (eps : J R X) -> (phi : K R X) -> Type
> (<>) {X} {R} eps phi = (p : X -> R) -> phi p = p (eps p)  

This trivially implies

> overlineLemma : {X, R : Type} -> (eps : J R X) -> eps <> overline eps
> overlineLemma eps = \ p => Refl

Then they give examples of selection functions that are compatible with
given quantifiers. One for the universal quantifier

< forevery : {X : Type} -> (xs : List X) -> NonEmpty xs -> K Bool X
< forevery xs ne p = not (forsome xs ne (not . p))

is |findnot|:

> findnot : {X : Type} -> (xs : List X) -> NonEmpty xs -> J Bool X
> findnot      Nil  _ p impossible
> findnot (x :: xs) _ p with (nonEmpty xs)
>   | (Yes prf) = if p x then find xs prf p else x
>   | ( No prf) = x

they argue. They first notice that

> findnotLemma : {X : Type} -> 
>                (xs : List X) -> (ne : NonEmpty xs) ->
>                (p : X -> Bool) -> findnot xs ne p = find xs ne (not . p)

and 

> foreveryFindnotLemma : {X : Type} -> 
>                        (xs : List X) -> (ne : NonEmpty xs) -> 
>                        (p : X -> Bool) -> 
>                        forevery xs ne p = overline (findnot xs ne) p

from which they conclude

> findnotForeveryLemma : {X : Type} -> 
>                        (xs : List X) -> (ne : NonEmpty xs) -> 
>                        findnot xs ne <> forevery xs ne
> findnotForeveryLemma xs ne p = ( forevery xs ne p )
>                              ={ foreveryFindnotLemma xs ne p }=
>                                ( overline (findnot xs ne) p )
>                              ={ overlineLemma (findnot xs ne) p }=
>                                ( p (findnot xs ne p) )
>                              QED




> {-

> SpecJ : {X : Type} -> (e : J Type X) -> (P : X -> Type) -> P (e P) -> (x ** P x) 

> SpecJ' : {X : Type} -> (e : J Type X) -> (P : X -> Type) -> (x ** P x) -> P (e P)

> Phi : {X : Type} -> (X -> Type) -> Type
> Phi P = (x ** P x) 

trivially

> Lemma : {X : Type} -> (e : J Type X) -> (P : X -> Type) -> Phi P -> P (e P)
> Lemma = SpecJ'

> Lemma' : {X : Type} -> (e : J Type X) -> (P : X -> Type) -> P (e P) -> Phi P
> Lemma' = SpecJ

but proving |phi p = p (e p)| as in the beginning Section 2.2

> HC : {X : Type} -> (e : J Type X) -> (P : X -> Type) -> Phi P = P (e P)

is not going to work I think. Perhaps we can try to implement some sort
of Hilbert's condition for the specific case in which properties are
represented by Boolean functions:

> specJ : {X : Type} -> (e : J Bool X) -> (p : X -> Bool) -> p (e p) = True -> (x ** p x = True) 

> specJ' : {X : Type} -> (e : J Bool X) -> (p : X -> Bool) -> (x ** p x = True) -> p (e p) = True

> phi : {X : Type} -> (X -> Bool) -> Type
> phi p = (x ** p x = True)

In this case one has trivially

> hc : {X : Type} -> (e : J Bool X) -> (p : X -> Bool) -> (exists : phi p) -> (p . fst) exists = p (e p)
> hc e p exists = ( (p . fst) exists )
>               ={ snd exists }=
>                 ( True )
>               ={ sym (specJ' e p exists)}=
>                 ( p (e p) )
>               QED
 
Is this what |phi p = p (e p)| is meant to say? The whole point of the
discussion about Hilbert's condition seems to be 


> ---}


 
