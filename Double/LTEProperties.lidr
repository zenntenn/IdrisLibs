> module Double.LTEProperties

> import Data.So

> import Double.Predicates
> import Double.Postulates
> import Double.LTEPostulates
> import Rel.TotalPreorder

> %default total
> %access public export


* |LTE| is a total preorder:

> ||| LTE is total
> totalLTE : (x, y : Double) -> Either (x `LTE` y) (y `LTE` x) 
> totalLTE x y with (compare x y) proof prf
>   | LT = Left  (MkLTE x y (LTinLTE (compareLT prf)))
>   | EQ = Left  (MkLTE x y (EQinLTE (compareEQ prf)))
>   | GT = Right (MkLTE y x (LTinLTE (gtLT (compareGT prf))))


> ||| LTE is a total preorder
> totalPreorderLTE : TotalPreorder Double.Predicates.LTE
> totalPreorderLTE = MkTotalPreorder LTE reflexiveLTE transitiveLTE totalLTE


* Properties of |LTE| and |sum|:

> ||| |sum| is monotone
> monotoneSum : {A : Type} ->
>               (f : A -> Double) -> (g : A -> Double) ->
>               (p : (a : A) -> f a `LTE` g a) ->
>               (as : List A) ->
>               sum (map f as) `LTE` sum (map g as)
> monotoneSum f g p Nil = reflexiveLTE 0.0               
> monotoneSum f g p (a :: as) = 
>   monotonePlusLTE {a = f a} {b = g a} {c = sum (map f as)} {d = sum (map g as)} (p a) (monotoneSum f g p as)


