> LTB : Nat -> Type
> LTB b = DPair Nat (\ n  => LT n b)

> implementation Uninhabited (LTB Z) where
>   uninhabited (MkDPair n prf) = absurd prf


> data LTE : Double -> Double -> Type where
>   MkLTE : {x : Double} -> {y : Double} -> So (x <= y) -> LTE x y

> NonNegDouble : Type
> NonNegDouble = Subset Double (\ x => 0.0 `LTE` x)

> toDouble : NonNegDouble -> Double
> toDouble = getWitness

> implementation Show NonNegDouble where
>   show = show . toDouble 
