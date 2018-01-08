> module NonNegDouble.Postulates

> import NonNegDouble.Properties
> import Double.Predicates
> import Double.Properties
> import NonNegDouble.NonNegDouble
> import NonNegDouble.BasicOperations
> import NonNegDouble.Properties
> import List.Operations


> %default total
> %access public export


* Properties of sums of products:

> using implementation NumNonNegDouble
>   postulate 
>   mapIdRightMultPreservesPositivity : 
>     {A : Type} ->
>     (axs : List (A, NonNegDouble)) -> 
>     Positive (toDouble (sumMapSnd axs)) ->
>     (y : NonNegDouble) -> 
>     Positive (toDouble y) ->
>     Positive (toDouble (sumMapSnd (mapIdRightMult (axs, y))))


> ||| 
> postulate 
> sumMapSndConsLemma1 : 
>   {A : Type} ->
>   (a : A) ->
>   (x : Double) ->
>   (px : Positive x) ->
>   (nnx : NonNegative x) ->
>   (axs : List (A, NonNegDouble)) -> 
>   Positive (toDouble (sumMapSnd ((a, Element x nnx) :: axs)))


> |||
> postulate 
> mvMultLemma : {A, B : Type} ->
>               (axs : List (A, NonNegDouble)) -> 
>               Positive (toDouble (sumMapSnd axs)) -> 
>               (f : A -> List (B, NonNegDouble)) -> 
>               ((a : A) -> Positive (toDouble (sumMapSnd (f a)))) ->
>               Positive (toDouble (sumMapSnd (mvMult axs f)))


> {-

> ---}
 
 
 
 
