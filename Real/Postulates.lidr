> module Real.Postulates


> %default total
> %access public export


* Reals

> ||| Real numbers
> postulate Real : Type 


* Constants

> ||| Zero
> postulate zero : Real


* Operations

> ||| 
> postulate fromNat : Nat -> Real

> ||| Addition of real numbers
> postulate plus : Real -> Real -> Real

> ||| Multiplication of real numbers
> postulate mult : Real -> Real -> Real

> ||| Subtrantion of real numbers
> postulate minus : Real -> Real -> Real

> ||| Division of real numbers
> postulate div : Real -> Real -> Real

> ||| Division of real numbers
> postulate abs : Real -> Real


* Relations (as predicates)

> ||| Smaller or equal
> postulate LTE : Real -> Real -> Type

> ||| Greater then
> GT : Real -> Real -> Type
> GT x y = Not (x `LTE` y)



> {-

> ---}
 
 
 
 
