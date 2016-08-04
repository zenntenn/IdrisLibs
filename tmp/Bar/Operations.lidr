> module Bar.Operations
> import Bar.Bar
> import Foo.Foo
> import Foo.Operations
> toFoo : Bar -> Foo
> toNat : Bar -> Nat
> toNat = Foo.Operations.toNat . toFoo




