> module Lecture1

> import Real.Postulates
> import Real.Properties
> import Real.Sequence
> import Fun.Properties
> import Sigma.Sigma
> import Pairs.Operations

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

> count : {A : Type} -> (Eq A) => (Nat -> A) -> Nat -> A -> Nat
> count f  Z    x = Z
> count f (S m) x with (count (f . S) m x) 
>   | res = if x == f Z
>           then S res
>           else   res


> using implementation FractionalReal
>   ||| relFreq x c 
>   relFreq : {A : Type} -> (Eq A) => Collective A -> Nat -> A -> Real
>   relFreq c  Z    x = zero
>   relFreq c (S m) x = fromNat (count c (S m) x) / (fromNat (S m))


> frequencies : {A : Type} -> (Eq A) => Collective A -> A -> Sequence
> frequencies c x = \ n => relFreq c n x


> hasLimits : {A : Type} -> (Eq A) => Collective A -> Type
> -- hasLimits c {A} = (x : A) -> Exists (\ l => hasLimit (frequencies c x) l)
> hasLimits c {A} = (x : A) -> Exists (hasLimit (frequencies c x))

** Two different pairs of dice


** Limiting value of relative frequency


** The probability of death


** First the collective - then the probability


** Probability in gas theory


** An historical remark


** Randomness


** Definition of randomness: place selection

> PlaceSelection : Type
> PlaceSelection = Sigma (Nat -> Nat) Injective1 

> select : {A : Type} -> Collective A -> PlaceSelection -> Collective A
> -- select c ps = c . (getWitness ps) 
> select c ps n = c ((getWitness ps) n) 

> isRandom1 : {A : Type} -> (Eq A) => (c : Collective A) -> Type
> isRandom1 {A} c = (ps : PlaceSelection) -> hasLimits (select c ps)

> isRandom2 : {A : Type} -> (Eq A) => (c : Collective A) -> hasLimits c -> isRandom1 c -> Type
> isRandom2 {A} c prf rc = 
>   (x : A) -> 
>   (ps : PlaceSelection) -> 
>   limit (frequencies (select c ps) x) ((rc ps) x) = limit (frequencies c x) (prf x)

> prob : {A : Type} -> (Eq A) => (c : Collective A) -> hasLimits c -> A -> Real
> prob c prf x = limit (frequencies c x) (prf x) -- getWitness (prf x)







> {-

> ---}


