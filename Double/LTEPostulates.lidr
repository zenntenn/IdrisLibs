> module Double.LTEPostulates

> import Double.Predicates

> %default total
> %access public export


* |LTE| is a preorder:

> ||| LTE is reflexive
> postulate 
> reflexiveLTE : (x : Double) -> x `LTE` x

> ||| LTE is transitive
> postulate 
> transitiveLTE : (x, y, z : Double) -> x `LTE` y -> y `LTE` z -> x `LTE` z


* Properties of |LTE| and |plus|:

> ||| LTE is monotone w.r.t. `plus`
> postulate
> monotonePlusLTE : {a, b, c, d : Double} -> 
>                   a `LTE` b -> c `LTE` d -> (a + c) `LTE` (b + d)


* Properties of |LTE| and |mult|:

> ||| LTE is monotone w.r.t. `(*)`
> postulate 
> monotoneMultLTE : {a, b, c, d : Double} -> 
>                   a `LTE` b -> c `LTE` d -> (a * c) `LTE` (b * d)


> {-

> ---}
 
 
