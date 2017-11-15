> module NonNegDouble.open_issues.Main

> %default total
> %access public export

> data Positive : Nat -> Type where
>   MkPositive  : {n : Nat} -> Positive (S n)

> PNat : Type
> PNat = Subset Nat Positive

> Fraction : Type
> Fraction = (Nat, PNat)

> data Normal : Fraction -> Type

> NonNegRational : Type
> NonNegRational = Subset Fraction Normal

> plus : NonNegRational -> NonNegRational -> NonNegRational

> mult : NonNegRational -> NonNegRational -> NonNegRational

> fromNat : (n : Nat) -> NonNegRational

> implementation Num NonNegRational where
>   (+) = plus
>   (*) = mult
>   fromInteger = fromNat . fromIntegerNat
