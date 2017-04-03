> module Double.Postulates

> import Data.So

> import Double.Predicates

> %default total
> %access public export
> %auto_implicits on


* Arithmetic

> ||| 
> postulate
> plusZeroLeftNeutral : {x : Double} -> 0.0 + x = x

> ||| 
> postulate
> plusZeroRightNeutral : {x : Double} -> x + 0.0 = x

> ||| 
> postulate
> multZeroLeftZero : {x : Double} -> 0.0 * x = 0.0

> ||| 
> postulate
> multZeroRightZero : {x : Double} -> x * 0.0 = 0.0

> |||
> postulate
> minusSelfZero : {x : Double} -> x - x = 0.0


* |LTE|:

> ||| LTE is reflexive
> postulate 
> reflexiveLTE : (x : Double) -> x `LTE` x

> ||| LTE is transitive
> postulate 
> transitiveLTE : (x, y, z : Double) -> x `LTE` y -> y `LTE` z -> x `LTE` z

> ||| LTE is monotone w.r.t. addition
> postulate
> monotonePlusLTE : {a, b, c, d : Double} -> 
>                   a `LTE` b -> c `LTE` d -> a + c `LTE` b + d

> ||| LTE is monotone w.r.t. multiplication
> postulate 
> monotoneMultLTE : {a, b, c, d : Double} -> 
>                   a `LTE` b -> c `LTE` d -> a * c `LTE` b * d

> ||| LTE is monotone w.r.t. "subtraction of a const"
> postulate
> monotoneMinusConstLTE : {a, b, c : Double} -> 
>                         a `LTE` b -> a - c `LTE` b - c

> ||| LTE is monotone w.r.t. "division by a const"
> postulate
> monotoneDivConstLTE : {a, b, c : Double} -> 
>                       a `LTE` b -> Positive c -> a / c `LTE` b / c


* Non-negative double precision floating point numbers:

> ||| Non-negative |Double|s are closed w.r.t. "subtraction"
> postulate 
> minusPreservesNonNegativity : {x, y : Double} -> 
>                               NonNegative x -> NonNegative y -> y `LTE` x -> NonNegative (x - y)

> ||| Non-negative |Double|s are closed w.r.t. division
> postulate 
> divPreservesNonNegativity : {x, y : Double} -> 
>                             NonNegative x -> NonNegative y -> NonNegative (x / y)


* Positive double precision floating point numbers:

> |||
> postulate 
> positivePlusAnyPositive : {x, y : Double} -> 
>                           Positive x -> NonNegative y -> Positive (x + y)


> ||| Positive |Double|s are closed w.r.t. division
> postulate 
> divPreservesPositivity : {x, y : Double} -> 
>                          Positive x -> Positive y -> Positive (x / y)

> |||
> postulate
> divPositiveSelfOne : {x : Double} -> Positive x -> x / x = 1.0


> |||
> postulate
> divZeroPositiveZero : {x : Double} -> Positive x -> 0.0 / x = 0.0


* Ord methods:

> |||
> postulate 
> gtLT : {x, y : Double} -> So (x > y) -> So (y < x)

> postulate 
> notCompareEQ : {x, y : Double} -> Not (So (x == y)) -> Not (EQ = compare x y)


