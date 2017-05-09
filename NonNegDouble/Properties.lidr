> module NonNegDouble.Properties

> import Data.So
> import Syntax.PreorderReasoning

> import Double.Predicates
> import Double.Postulates
> import Double.Properties
> import NonNegDouble.NonNegDouble
> import NonNegDouble.Constants
> import NonNegDouble.BasicOperations
> import NonNegDouble.Operations
> import List.Operations


> %default total
> %access public export


* Positivity of constants

> ||| zero is not positive
> notPositiveZero : Not (Positive (toDouble NonNegDouble.Constants.zero))
> notPositiveZero = s3 where
>   s0 : toDouble (Element 0.0 (MkLTE Oh)) = 0.0
>   s0 = Refl
>   s1 : Element 0.0 (MkLTE Oh) = NonNegDouble.Constants.zero
>   s1 = Refl
>   s2 : toDouble NonNegDouble.Constants.zero = 0.0
>   s2 = replace {P = \ X => toDouble X = 0.0} s1 s0  
>   s3 : Not (Positive (toDouble NonNegDouble.Constants.zero))
>   s3 = replace {P = \ X => Not (Positive X)} (sym s2) Double.Properties.notPositiveZero 

> ||| one is positive
> positiveOne : Positive (toDouble NonNegDouble.Constants.one)
> positiveOne = MkLT Oh


* Implementations:

> ||| NonNegDouble is an implementation of Show
> implementation Show NonNegDouble where
>   show = show . toDouble 

> ||| NonNegDouble is an implementation of Num
> implementation Num NonNegDouble where
>   (+) = plus
>   (*) = mult
>   fromInteger = fromNat . fromIntegerNat

> ||| NonNegDouble is an implementation of Fractional
> implementation Fractional NonNegDouble where
>   (/) = div

> ||| NonNegDouble is an implementation of Eq
> implementation Eq NonNegDouble where
>   (==) x y = (toDouble x) == (toDouble y)

> ||| NonNegDouble is an implementation of Ord
> implementation Ord NonNegDouble where
>   compare x y = compare (toDouble x) (toDouble y)


* Properties of |toDouble|:

> ||| 
> toDoublePlusLemma : (x : NonNegDouble) -> (y : NonNegDouble) -> toDouble (x + y) = (toDouble x) + (toDouble y)
> toDoublePlusLemma (Element x px) (Element y py) = 
>     ( toDouble ((Element x px) + (Element y py)) )
>   ={ Refl }=
>     ( toDouble (plus (Element x px) (Element y py)) )
>   ={ Refl }=
>     ( toDouble (Element (x + y) (plusPreservesNonNegativity px py)) )
>   ={ Refl }=
>     ( x + y )
>   ={ Refl }=
>     ( (toDouble (Element x px)) + (toDouble (Element y py)) )
>   QED

> ||| 
> toDoubleMultLemma : (x : NonNegDouble) -> (y : NonNegDouble) -> toDouble (x * y) = (toDouble x) * (toDouble y)
> toDoubleMultLemma (Element x px) (Element y py) = 
>     ( toDouble ((Element x px) * (Element y py)) )
>   ={ Refl }=
>     ( toDouble (mult (Element x px) (Element y py)) )
>   ={ Refl }=
>     ( toDouble (Element (x * y) (multPreservesNonNegativity px py)) )
>   ={ Refl }=
>     ( x * y )
>   ={ Refl }=
>     ( (toDouble (Element x px)) * (toDouble (Element y py)) )
>   QED

> ||| 
> toDoubleDivLemma : (x : NonNegDouble) -> (y : NonNegDouble) -> toDouble (x / y) = (toDouble x) / (toDouble y)
> toDoubleDivLemma (Element x px) (Element y py) = 
>     ( toDouble ((Element x px) / (Element y py)) )
>   ={ Refl }=
>     ( toDouble (div (Element x px) (Element y py)) )
>   ={ Refl }=
>     ( toDouble (Element (x / y) (divPreservesNonNegativity px py)) )
>   ={ Refl }=
>     ( x / y )
>   ={ Refl }=
>     ( (toDouble (Element x px)) / (toDouble (Element y py)) )
>   QED


* Properties entailed by postulates and properties of |Double|s:

> |||
> divPreservesPositivity : {x, y : NonNegDouble} -> 
>                          Positive (toDouble x) -> Positive (toDouble y) -> Positive (toDouble (x / y))
> divPreservesPositivity {x} {y} pdx pdy = replace s1 s2 where
>   s1 : (toDouble x) / (toDouble y) = toDouble (x / y)
>   s1 = sym (toDoubleDivLemma x y)
>   s2 : Positive ((toDouble x) / (toDouble y))
>   s2 = Double.Postulates.divPreservesPositivity pdx pdy


> {-

> ---}
