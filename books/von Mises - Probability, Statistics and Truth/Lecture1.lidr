> module Lecture1

> import Real.Postulates
> import Real.Properties
> import Real.Sequence

> %default total
> %access public export
> %auto_implicits off

* The Definition of Probability


** Amendment of popular terminology


** Explanation of words


** Synthetic definitions


** Terminology


** The concept of work in mechanics


** An historical interlude


** The purpose of rational concepts


** The inadequacy of theories


** Limitation of scope


** Unlimited repetition


** The collective

... 

We must now introduce a new term, which will be very useful during the
future course of our argument. This term is 'the collective', and it
denotes a sequence of uniform events or processes which differ by
certain observable attributes, say colours, numbers, or anything else.


> Collective : Type -> Type
> Collective A = Nat -> A

...


** The first step towards a definition

> count : {A : Type} -> (Eq A) => A -> (Nat -> A) -> Nat -> Nat
> count x f  Z    = Z
> count x f (S m) with (count x (f . S) m) 
>   | res = if x == f Z
>           then S res
>           else   res

> {-

> using implementation FractionalReal
>   ||| relFreq x c 
>   relFreq : {A : Type} -> (Eq A) => A -> Collective A -> Nat -> Real
>   relFreq x c  Z    = zero
>   relFreq x c (S m) = fromNat (count x c (S m)) / (fromNat (S m))


> frequencies : {A : Type} -> (Eq A) => A -> Collective A -> Sequence
> frequencies x c = \ n => relFreq x c n


> hasLimits : {A : Type} -> (Eq A) => Collective A -> Type
> hasLimits c {A} = (x : A) -> Exists (\ l => hasLimit (frequencies x c) l)


> prob : {A : Type} -> (Eq A) => (c : Collective A) -> hasLimits c -> A -> Real
> prob c prf x = getWitness (prf x)



** Two different pairs of dice

** Limiting value of relative frequency

> ---}


