> data OnOff = On | Off
 
> Foo : Nat -> Type
> Foo t = OnOff

> [lala] Eq OnOff where
>   (==)  On  On = True
>   (==)  On Off = False
>   (==) Off  On = False
>   (==) Off Off = True

> EqFoo : {t : Nat} -> Eq (Foo t)
> EqFoo = lala 

> Bar : (t : Nat) -> Foo t -> Type

> EqBar : {t : Nat} -> {f : Foo t} -> Eq (Bar t f)

> FooBar : Nat -> Type
> FooBar t = DPair (Foo t) (Bar t) 

> using (t : Nat)
>   implementation Eq (FooBar t) where
>     (==) (MkDPair f b) (MkDPair f' b') = if (==) @{EqFoo} f f'
>                                          then (==) @{EqBar} b b'
>                                          else False

> data FooBarSeq : (t : Nat) -> (n : Nat) -> Type where
>   Nil  : {t : Nat} -> (x : Foo t) -> FooBarSeq t Z
>   (::) : {t, n : Nat} -> (FooBar t) -> FooBarSeq (S t) n -> FooBarSeq t (S n)

> {-
> using (t : Nat)
>   implementation (Eq (Foo t), Eq (FooBar t)) => Eq (FooBarSeq t n) | t where
>     (==)     (Nil x)      (Nil x') = x == x'
>     (==) (xy :: xys) (xy' :: xys') = if xy == xy' 
>                                      then xys == xys'
>                                      else False
> -}

