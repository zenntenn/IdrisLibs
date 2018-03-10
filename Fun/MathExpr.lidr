> module Fun.MathExpr

from https://github.com/DSLsofMath/DSLsofMath/blob/master/L/DSLsofMath/FunExp.lhs

> import Interfaces.Math

> %default total
> %access public export
> %auto_implicits on -- off


> ||| Functions as expressions
> data MathExpr : Type -> Type where
>   Id    : MathExpr t
>   Neg   : MathExpr t
>   Exp   : MathExpr t
>   Sin   : MathExpr t
>   Cos   : MathExpr t
>   Const : t -> MathExpr t
>   (+)   : MathExpr t -> MathExpr t -> MathExpr t
>   (-)   : MathExpr t -> MathExpr t -> MathExpr t
>   (*)   : MathExpr t -> MathExpr t -> MathExpr t
>   (/)   : MathExpr t -> MathExpr t -> MathExpr t
>   (.)   : MathExpr t -> MathExpr t -> MathExpr t


> ||| Evaluation
> eval : (Num t, Fractional t, Neg t, Math t) => MathExpr t -> t -> t
> eval Id        x = id x
> eval Neg       x = - x
> eval Exp       x = exp x
> eval Sin       x = sin x
> eval Cos       x = cos x
> eval (Const c) x = (const c) x 
> eval (e1 + e2) x = (eval e1 x) + (eval e2 x)
> eval (e1 - e2) x = (eval e1 x) - (eval e2 x)
> eval (e1 * e2) x = (eval e1 x) * (eval e2 x)
> eval (e1 / e2) x = (eval e1 x) / (eval e2 x)
> eval (e1 . e2) x = (eval e1 (eval e2 x))


> ||| Differentiation
> derivative : (Num t, Fractional t, Neg t) => MathExpr t -> MathExpr t
> derivative Id        = Const 1
> derivative Neg       = Const (negate 1)
> derivative Exp       = Exp
> derivative Sin       = Cos
> derivative Cos       = Neg . Sin
> derivative (Const c) = Const 0
> derivative (e1 + e2) = derivative e1 + derivative e2 
> derivative (e1 - e2) = derivative e1 - derivative e2 
> derivative (e1 * e2) = (derivative e1) * e2 + e1 * (derivative e2)  
> derivative (e1 / e2) = (derivative e1) / e2 - e1 * (derivative e2) / (e2 * e2)
> derivative (e1 . e2) = ((derivative e1) . e2) * (derivative e2)  

This needs to be tested!
