> module NonNegDouble.LTEProperties

> import NonNegDouble.NonNegDouble
> import NonNegDouble.Constants
> import NonNegDouble.Predicates
> import NonNegDouble.BasicOperations
> import NonNegDouble.BasicProperties
> import Double.Predicates
> import Double.LTEPostulates
> import Double.Properties
> import Double.LTEProperties
> import Rel.TotalPreorder 

> %default total
> %access public export


* |LTE| is a total preorder:

> ||| LTE is reflexive
> reflexiveLTE : (x : NonNegDouble) -> x `LTE` x
> reflexiveLTE x = reflexiveLTE (toDouble x)


> ||| LTE is transitive
> transitiveLTE : (x, y, z : NonNegDouble) -> x `LTE` y -> y `LTE` z -> x `LTE` z
> transitiveLTE x y z xLTEy yLTEz = transitiveLTE (toDouble x) (toDouble y) (toDouble z) xLTEy yLTEz


> ||| LTE is total
> totalLTE : (x, y : NonNegDouble) -> Either (x `LTE` y) (y `LTE` x) 
> totalLTE x y = totalLTE (toDouble x) (toDouble y)


> ||| LTE is a total preorder
> totalPreorderLTE : TotalPreorder NonNegDouble.Predicates.LTE
> totalPreorderLTE = MkTotalPreorder LTE reflexiveLTE transitiveLTE totalLTE


* Properties of |LTE| and |plus|:

> ||| LTE is monotone w.r.t. `(+)`
> monotonePlusLTE : {a, b, c, d : NonNegDouble} -> 
>                   a `LTE` b -> c `LTE` d -> (a + c) `LTE` (b + d)
> monotonePlusLTE {a} {b} {c} {d} aLTEb cLTEd = s3 where
>   s1 : (toDouble a) + (toDouble c) `LTE` (toDouble b) + (toDouble d)
>   s1 = monotonePlusLTE {a = toDouble a} {b = toDouble b} {c = toDouble c} {d = toDouble d} aLTEb cLTEd
>   s2 : toDouble (a + c) `LTE` (toDouble b) + (toDouble d)
>   s2 = replace {P = \ X => X `LTE` (toDouble b) + (toDouble d)} (sym (toDoublePlusLemma a c)) s1
>   s3 : toDouble (a + c) `LTE` toDouble (b + d)
>   s3 = replace {P = \ X => toDouble (a + c) `LTE` X} (sym (toDoublePlusLemma b d)) s2


* Properties of |LTE| and |mult|:

> ||| LTE is monotone w.r.t. `(*)`
> monotoneMultLTE : {a, b, c, d : NonNegDouble} -> 
>                   a `LTE` b -> c `LTE` d -> (a * c) `LTE` (b * d)
> monotoneMultLTE {a} {b} {c} {d} aLTEb cLTEd = s3 where
>   s1 : (toDouble a) * (toDouble c) `LTE` (toDouble b) * (toDouble d)
>   s1 = monotoneMultLTE {a = toDouble a} {b = toDouble b} {c = toDouble c} {d = toDouble d} aLTEb cLTEd
>   s2 : toDouble (a * c) `LTE` (toDouble b) * (toDouble d)
>   s2 = replace {P = \ X => X `LTE` (toDouble b) * (toDouble d)} (sym (toDoubleMultLemma a c)) s1
>   s3 : toDouble (a * c) `LTE` toDouble (b * d)
>   s3 = replace {P = \ X => toDouble (a * c) `LTE` X} (sym (toDoubleMultLemma b d)) s2


* Properties of |LTE| and |sum|:

> ||| |sum| is monotone
> monotoneSum : {A : Type} ->
>               (f : A -> NonNegDouble) -> (g : A -> NonNegDouble) ->
>               (p : (a : A) -> f a `LTE` g a) ->
>               (as : List A) ->
>               sum (map f as) `LTE` sum (map g as)
> monotoneSum f g p Nil = reflexiveLTE 0.0
> monotoneSum f g p (a :: as) = 
>   monotonePlusLTE {a = f a} {b = g a} {c = sum (map f as)} {d = sum (map g as)} (p a) (monotoneSum f g p as)

> {-

> ---}
 
