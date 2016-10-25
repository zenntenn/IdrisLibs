> module Matrix.Operations

> import Data.Fin
> import Data.Vect

> import Matrix.Matrix

> %default total
> %access public export
> %auto_implicits on


> row : (Fin m) -> Matrix m n t -> Vect n t
> row k xss = index k xss


> toVect : Matrix m n t -> Vect (m * n) t
> toVect = concat
