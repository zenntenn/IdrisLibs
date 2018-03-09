> module Fun.MathExpr

from https://github.com/DSLsofMath/DSLsofMath/blob/master/L/DSLsofMath/FunExp.lhs

> %default total
> %access public export
> %auto_implicits on -- off


> ||| Functions as expressions
> data MathExpr : Type -> Type where
>   Const : t -> MathExpr t
>   Id    : MathExpr t
>   Neg   : MathExpr t -> MathExpr t
>   (+)   : MathExpr t -> MathExpr t -> MathExpr t
>   (-)   : MathExpr t -> MathExpr t -> MathExpr t
>   (*)   : MathExpr t -> MathExpr t -> MathExpr t
>   (/)   : MathExpr t -> MathExpr t -> MathExpr t
>   (.)   : MathExpr t -> MathExpr t -> MathExpr t
>   Exp   : MathExpr t -> MathExpr t
>   -- etc.


> interface (Num ty) => Math ty where
>   exp : ty -> ty 

> implementation Math Double where
>   exp = Prelude.Doubles.exp


> ||| Evaluation
> eval : (Num t, Fractional t, Neg t, Math t) => MathExpr t -> t -> t
> eval (Const c) x = (const c) x 
> eval Id        x = id x
> eval (Neg e)   x = - (eval e x)
> eval (e1 + e2) x = (eval e1 x) + (eval e2 x)
> eval (e1 - e2) x = (eval e1 x) - (eval e2 x)
> eval (e1 * e2) x = (eval e1 x) * (eval e2 x)
> eval (e1 / e2) x = (eval e1 x) / (eval e2 x)
> eval (e1 . e2) x = (eval e1 (eval e2 x))
> eval (Exp e)   x = exp (eval e x)


> ||| Differentiation
> derivative : (Num t, Fractional t, Neg t) => MathExpr t -> MathExpr t
> derivative (Const c) = Const 0
> derivative Id        = Const 1
> derivative (Neg e)   = Neg (derivative e)
> derivative (e1 + e2) = derivative e1 + derivative e2 
> derivative (e1 - e2) = derivative e1 - derivative e2 
> derivative (e1 * e2) = (derivative e1) * e2 + e1 * (derivative e2)  
> derivative (e1 / e2) = (derivative e1) / e2 - e1 * (derivative e2) / (e2 * e2)
> derivative (e1 . e2) = ((derivative e1) . e2) * (derivative e2)  
> derivative (Exp e)   = (Exp e) * (derivative e)

This needs to be tested!
