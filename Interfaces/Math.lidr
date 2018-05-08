> module Interfaces.Math

> %default total
> %access public export
> %auto_implicits off


> interface (Num ty) => Math ty where
>   exp : ty -> ty 
>   sin : ty -> ty 
>   cos : ty -> ty 


