> module Prob.Prob

> import Data.So
> import Syntax.PreorderReasoning

> import So.Properties
> import Real.Postulates
> import Real.Properties

> %default total
> %access public export
> %auto_implicits off


* Propositions

> infixr 4 ||
> infixr 5 && 
> infixr 7 <=> 

> Prop : Type

> top : Prop

> neg : Prop -> Prop

> (||) : Prop -> Prop -> Prop

> (&&) : Prop -> Prop -> Prop

> bot : Prop
> bot = neg top
 
> (<=>) : Prop -> Prop -> Type

> reflexive : {p : Prop} -> p <=> p

> symmetric : {p, q : Prop} -> p <=> q -> q <=> p

> transitive : {p, q, r : Prop} -> p <=> q -> q <=> r -> p <=> r


* Probability theory: axioms

> prob : Prop -> Real

> using implementation NumReal, NegReal

>   A1 : (a : Prop) -> 0 `LTE` prob a 

>   A2 : prob top = 1

>   A3 : (a, b : Prop) -> a && b = bot -> prob (a || b) = prob a + prob b


* Probability theory: theorems

>   T5 : (a : Prop) -> prob (neg a) = 1 - prob a

>   T6 : prob bot = 0
>   T6 = ( prob bot )
>      ={ Refl }=
>        ( prob (neg top) )
>      ={ T5 top }=
>        ( 1 - prob top )
>      ={ cong A2 }=
>        ( 1 - 1 )  
>      ={ minusLemma }=
>        ( 0 )
>      QED

>   T7 : (a, b : Prop) -> a <=> b -> prob a = prob b
>   T7 a b prf = ( prob a ) 
>              ={ ?lika }=
>                ( prob b )
>              QED


> {-

> ---}
 
