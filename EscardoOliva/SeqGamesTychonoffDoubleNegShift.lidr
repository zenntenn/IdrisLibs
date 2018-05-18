> module SeqGamesTychonoffDoubleNegShift

> import Syntax.PreorderReasoning

> %default total
> %access public export
> %auto_implicits off

> ||| Selection functions
> J : Type -> Type -> Type
> J R X = (X -> R) -> X

> ||| Generalized quantifiers
> K : Type -> Type -> Type
> K R X = (X -> R) -> R

> bigotimes : {X, R : Type} -> List (J R X) -> J R (List X)
> bigotimes  Nil      p = Nil
> bigotimes (e :: es) p = x0 :: bigotimes es (p . (x0 ::)) where
>   x0 = e (\ x => p (x :: bigotimes es (p . (x ::))))

> overline : {X, R : Type} -> J R X -> K R X
> overline e = \ p => p (e p)

> partial
> find : {X : Type} -> List X -> J Bool X
> find (x :: Nil) p = x
> find (x ::  xs) p = if p x then x else find xs p

> partial
> forsome : {X : Type} -> List X -> K Bool X
> forsome = overline . find

> partial
> forevery : {X : Type} -> List X -> K Bool X
> forevery xs p = not (forsome xs (not . p))

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
 
Is this what |phi p = p (e p)| is meant to say?





 
