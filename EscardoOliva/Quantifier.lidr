> module EscadoOliva.Quantifier

> %default total
> %access public export
> %auto_implicits off


> ||| Quantifier
> K : Type -> Type -> Type
> K R X = (X -> R) -> R


