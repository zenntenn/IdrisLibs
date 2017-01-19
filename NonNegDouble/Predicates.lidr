> module NonNegDouble.Predicates

> import NonNegDouble.NonNegDouble
> import NonNegDouble.BasicOperations
> import Double.Predicates

> %default total
> %access public export
> %auto_implicits off


> ||| Proofs that `x` is less than or equal to `y`                                                                          
> ||| @ x the smaller number                                                                                                
> ||| @ y the larger number
> LTE : (x, y : NonNegDouble) -> Type
> LTE x y = LTE (toDouble x) (toDouble y) 





