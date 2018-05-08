> module Fun.FunExp

from https://github.com/DSLsofMath/DSLsofMath/blob/master/L/DSLsofMath/FunExp.lhs

> %default total
> %access public export
> %auto_implicits on -- off


> ||| Functions as expressions
> data FunExp : Type -> Type where
>   Const : t -> FunExp t
>   Id    : FunExp t
>   (+)   : FunExp t -> FunExp t -> FunExp t
>   (-)   : FunExp t -> FunExp t -> FunExp t
>   (*)   : FunExp t -> FunExp t -> FunExp t
>   (/)   : FunExp t -> FunExp t -> FunExp t
>   (.)   : FunExp t -> FunExp t -> FunExp t
>   Exp   : FunExp t -> FunExp t
>   -- etc.


> interface (Num ty) => Math ty where
>   exp : ty -> ty 


> ||| Evaluation
> eval : (Num t, Fractional t, Neg t, Math t) => FunExp t -> t -> t
> eval (Const c) x = (const c) x 
> eval Id        x = id x
> eval (e1 + e2) x = (eval e1 x) + (eval e2 x)
> eval (e1 - e2) x = (eval e1 x) - (eval e2 x)
> eval (e1 * e2) x = (eval e1 x) * (eval e2 x)
> eval (e1 / e2) x = (eval e1 x) / (eval e2 x)
> eval (e1 . e2) x = (eval e1 (eval e2 x))
> eval (Exp e)   x = exp (eval e x)


> ||| Differentiation
> derivative : (Num t, Fractional t, Neg t) => FunExp t -> FunExp t
> derivative (Const c) = Const 0
> derivative Id        = Const 1
> derivative (e1 + e2) = derivative e1 + derivative e2 
> derivative (e1 - e2) = derivative e1 - derivative e2 
> derivative (e1 * e2) = (derivative e1) * e2 + e1 * (derivative e2)  
> derivative (e1 / e2) = (derivative e1) / e2 - e1 * (derivative e2) / (e2 * e2)
> derivative (e1 . e2) = ((derivative e1) . e2) * (derivative e2)  
> derivative (Exp e)   = (Exp e) * (derivative e)

This needs to be tested!
