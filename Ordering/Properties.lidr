> module Ordering.Properties

> %default total
> %access public export
> %auto_implicits on


> |||
> Uninhabited (LT = EQ) where                                                                                               
>   uninhabited Refl impossible

> |||
> Uninhabited (Prelude.Interfaces.LT = GT) where
>   uninhabited Refl impossible

> |||
> Uninhabited (EQ = GT) where
>   uninhabited Refl impossible

> |||
> Uninhabited (EQ = LT) where
>   uninhabited Refl impossible

> |||
> Uninhabited (Prelude.Interfaces.GT = LT) where
>   uninhabited Refl impossible

> |||
> Uninhabited (GT = EQ) where
>   uninhabited Refl impossible

