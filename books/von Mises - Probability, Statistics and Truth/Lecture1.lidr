> module Lecture1

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

> Real : Type

> Sequence : Type
> Sequence = Nat -> Real

> Lala : Real -> Real -> Type

> hasLimit : Sequence -> Real -> Type
> hasLimit f x = (eps : Real) -> eps `Lala` 0 -> existsNat (P f x eps) where
>   P         : Sequence -> Real -> Real -> Nat -> Type
>   p f x eps N = (n : Nat) -> N `LTE` n -> abs (f n - x) `LTE` eps 
>   existsNat : (Nat -> Type) -> Type
>   existsNat Q = Exists {a = Nat} (\ N => Q N)

> count : {A : Type} -> (Eq A) => A -> (Nat -> A) -> Nat -> Nat
> count x f  Z    = Z
> count x f (S m) with (count x (f . S) m) 
>   | res = if x == f Z
>           then S res
>           else   res

> partial 
> freq : {A : Type} -> (Eq A) => A -> Collective A -> Nat -> Double
> freq x c (S m) = num / den where
>   num : Double
>   num = cast (count x c (S m))
>   den : Double
>   den = cast (S m)

** Two different pairs of dice

** Limiting value of relative frequency



