> %default total
> %auto_implicits off

> Foo : Type
> Bar : Foo -> Type
> foo : (x : Foo) -> Bar x -> Foo
> bar : (x : Foo) -> Bar x -> Foo -> Nat

> Pol : Type
> Pol = (x : Foo) -> Bar x

> val : Foo -> Pol -> Nat

> Opt : Pol -> Type
> Opt = \ p => (x : Foo) -> (p' : Pol) -> val x p' `LTE` val x p

> opt : Pol

> prf : Opt opt
> prf = \ x => \ p' => ?kika

> val = \ x => \ p => let y  = p x in
>                     let x' = foo x y in
>                     assert_total (bar x y x' `plus` val x' p)
