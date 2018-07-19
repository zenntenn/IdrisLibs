> %default total
> %access public export
> %auto_implicits off

> FixPoint : {X : Type} -> X -> (X -> X) -> Type
> FixPoint x f = x = f x

> X : Type

> Y : X -> Type
> -- Y : Type

> P : Type
> P = (x : X) -> Y x
> -- P = X -> Y

> lemma : (p : P) -> (f : P -> P) -> FixPoint p f -> (x : X) -> p x = f p x
> lemma p f prf x = replace {P = \ T => p x = T x} prf Refl


