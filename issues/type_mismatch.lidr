> module issues.type_mismatch

> %default total
> %access public export
> %auto_implicits off

> M        : Type -> Type
> fmap     : {A, B : Type} -> (A -> B) -> (M A -> M B)
> ret      : {A : Type} -> A -> M A
> bind     : {A, B : Type} -> M A -> (A -> M B) -> M B
> Elem     : {A : Type} -> A -> M A -> Type
> NotEmpty : {A : Type} -> M A -> Type
> All      : {A : Type} -> (P : A -> Type) -> M A -> Type
> tagElem  : {A : Type} -> (ma : M A) -> M (DPair A (\ a => a `Elem` ma))
> allElemS : {A : Type} -> {P : A -> Type} ->
>            (a : A) -> (ma : M A) -> All P ma -> a `Elem` ma -> P a

> Foo : (t : Nat) -> Type
> Bar : (t : Nat) -> (x : Foo t) -> Type
> foo : (t : Nat) -> (x : Foo t) -> (y : Bar t x) -> M (Foo (S t))

> Open : {t : Nat} -> (n : Nat) -> Foo t -> Type

> Good : (t : Nat) -> (x : Foo t) -> (n : Nat) -> (Bar t x) -> Type
> Good t x n y = (NotEmpty (foo t x y), All (Open {t = S t} n) (foo t x y))

> GoodBar : (t : Nat) -> (x : Foo t) -> (n : Nat) -> Type
> GoodBar t x n = DPair (Bar t x) (Good t x n)

> allOpen : {t, n : Nat} -> {x : Foo t} -> (y : GoodBar t x n) -> All (Open n) (foo t x (fst y)) 
> allOpen (MkDPair _ p) = snd p

> Pol : (t : Nat) -> (n : Nat) -> Type
> Pol t  Z    = Unit
> Pol t (S m) = (x : Foo t) -> Open (S m) x -> GoodBar t x m

> data PolSeq : (t : Nat) -> (n : Nat) -> Type where
>   MkNilPolSeq : {t : Nat} -> PolSeq t Z
>   (::)        : {t, n : Nat} -> Pol t (S n) -> PolSeq (S t) n -> PolSeq t (S n)

> data FooBarSeq : (t : Nat) -> (n : Nat) -> Type where
>   MkNilFooBarSeq : {t : Nat} -> (x : Foo t) -> FooBarSeq t Z
>   (++)           : {t, n : Nat} -> DPair (Foo t) (Bar t) -> FooBarSeq (S t) n -> FooBarSeq t (S n)

 
> eps : {A : Type} -> M A -> A

> run : {t, n : Nat} -> 
>       (x : Foo t) -> (v : Open n x) ->
>       (ps : PolSeq t n) ->
>       FooBarSeq t n
> run {t} {n = Z}    x v MkNilPolSeq = MkNilFooBarSeq x
> run {t} {n = S m}  x v (p :: ps')  =
>   (MkDPair x y) ++ (eps (fmap f (tagElem mx'))) where
>     y   : Bar t x
>     y   = fst (p x v)
>     mx' : M (Foo (S t))
>     mx' = foo t x y
>     av  : All (Open m) mx'
>     av  = allOpen (p x v)
>     f   : DPair (Foo (S t)) (\ x' => x' `Elem` mx') -> FooBarSeq (S t) m
>     f (MkDPair x' x'emx') = run x' v' ps' where
>       v' : Open m x'
>       v' = allElemS x' mx' av x'emx'

> bar : {t, n : Nat} -> (x : Foo t) -> (v : Open n x) ->
>       (ps : PolSeq t n) -> M (FooBarSeq t n)
> bar {t} {n = Z}    x v MkNilPolSeq =  ret (MkNilFooBarSeq x)
> bar {t} {n = S m}  x v (p :: ps')  =
>   fmap g (bind (tagElem mx') f) where
>     y   :  Bar t x
>     y   =  fst (p x v)
>     mx' :  M (Foo (S t))
>     mx' =  foo t x y
>     av  :  All (Open m) mx'
>     av  =  allOpen (p x v)
>     g   :  FooBarSeq (S t) m -> FooBarSeq t (S m)
>     g   =  ((MkDPair x y) ++)
>     f   :  DPair (Foo (S t)) (\ x' => x' `Elem` mx') -> M (FooBarSeq (S t) m)
>     f (MkDPair x' x'emx') = bar {n = m} x' v' ps' where
>       v'  :  Open m x'
>       v'  =  allElemS x' mx' av x'emx'
