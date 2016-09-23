> module Fun.Predicates


> %default total
> %access public export
> %auto_implicits off


> ||| Extensional equality
> ExtEq : {A, B : Type} -> (f : A -> B) -> (g : A -> B) -> Type
> ExtEq {A} {B} f g = (a : A) -> f a = g a
