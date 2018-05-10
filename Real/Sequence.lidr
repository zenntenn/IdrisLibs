> module Real.Sequence

> import Real.Postulates
> import Real.Properties

> %default total
> %access public export


> ||| Sequences as functions 
> Sequence : Type
> Sequence = Nat -> Real


> using implementation NegReal
>   hasLimit : Sequence -> Real -> Type
>   hasLimit f x = (eps : Real) -> eps `GT` zero -> Exists (\ N => P f x eps N) where
>     P         : Sequence -> Real -> Real -> Nat -> Type
>     P f x eps N = (n : Nat) -> n `GT` N -> abs (f n - x) `LTE` eps 

> limit : (s : Sequence) -> Exists (hasLimit s) -> Real
> limit s = getWitness



> {-

> ---}





