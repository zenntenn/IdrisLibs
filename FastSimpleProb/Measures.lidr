> module FastSimpleProb.Measures

> import Data.So
> import Syntax.PreorderReasoning

> import FastSimpleProb.SimpleProb
> import FastSimpleProb.BasicOperations
> import FastSimpleProb.MonadicOperations
> import FastSimpleProb.MonadicProperties
> import Double.Predicates
> import NonNegDouble.NonNegDouble
> import NonNegDouble.Predicates
> import NonNegDouble.BasicProperties
> import NonNegDouble.Measures
> import NonNegDouble.MeasureProperties
> import NonNegDouble.LTEProperties
> import List.Operations
> import List.Properties
> import Fun.Operations
> import Rel.TotalPreorder

> %default total
> %access public export
> %auto_implicits off


* Measures

> ||| Worst
> worst : SimpleProb NonNegDouble -> NonNegDouble
> worst sp = List.Operations.min totalPreorderLTE xs ne where
>   xs : List NonNegDouble
>   xs = map fst (toList sp)
>   ne : List.Operations.NonEmpty xs
>   ne = mapPreservesNonEmpty fst (toList sp) (nonEmptyLemma1 sp)

> ||| Average
> average : SimpleProb NonNegDouble -> NonNegDouble
> average = average . (map (uncurry (*))) . toList

> ||| Expected value
> expectedValue : SimpleProb NonNegDouble -> NonNegDouble
> expectedValue = average


* Monotonicity of measures

> |||
> monotoneUncurryMultCrossId : {A : Type} ->
>                              (f : A -> NonNegDouble) -> (g : A -> NonNegDouble) ->
>                              (p : (a : A) -> f a `LTE` g a) ->
>                              (ap : (A, NonNegDouble)) ->
>                              uncurry (*) ((cross f id) ap) `LTE` uncurry (*) ((cross g id) ap)
> monotoneUncurryMultCrossId {A} f g p (a, x) = s3 where
>   s1 : f a `LTE` g a
>   s1 = p a
>   s2 : (f a) * x `LTE` (g a) * x
>   s2 = monotoneMultLTE s1 (reflexiveLTE x)
>   s3 : uncurry (*) ((cross f id) (a, x)) `LTE` uncurry (*) ((cross g id) (a, x))
>   s3 = s2

> ||| |worst| is monotone
> postulate
> monotoneWorst : {A : Type} ->
>                 (f : A -> NonNegDouble) -> (g : A -> NonNegDouble) ->
>                 (p : (a : A) -> f a `LTE` g a) ->
>                 (sp : SimpleProb A) ->
>                  worst (fmap f sp) `LTE` worst (fmap g sp)

> ||| |average| is monotone
> monotoneAverage : {A : Type} ->
>                   (f : A -> NonNegDouble) -> (g : A -> NonNegDouble) ->
>                   (p : (a : A) -> f a `LTE` g a) ->
>                   (sp : SimpleProb A) ->
>                   average (fmap f sp) `LTE` average (fmap g sp)
> monotoneAverage {A} f g p sp = s6 where
>   f'  : (A, NonNegDouble) -> NonNegDouble
>   f'  = uncurry (*) . (cross f id)
>   g'  : (A, NonNegDouble) -> NonNegDouble
>   g'  = uncurry (*) . (cross g id)
>   p'  : (ap : (A, NonNegDouble)) -> f' ap `LTE` g' ap
>   p'  = monotoneUncurryMultCrossId f g p 
>   aps : List (A, NonNegDouble)
>   aps = toList sp
>   s1  : average (map f' aps) `LTE` average (map g' aps)
>   s1  = monotoneAverage {A = (A, NonNegDouble)} f' g' p' aps 
>   s2  : map f' aps = map (uncurry (*)) (toList (fmap f sp))
>   s2  = ( map f' aps )
>       ={ Refl }=
>         ( map ((uncurry (*)) . (cross f id)) aps )
>       ={ sym (mapFusion (uncurry (*)) (cross f id) aps) }=
>         ( map (uncurry (*)) (fmap (cross f id) aps) )  
>       ={ cong (sym (toListFmapLemma f sp)) }=
>         ( map (uncurry (*)) (toList (fmap f sp)) )
>       QED
>   s3  : map g' aps = map (uncurry (*)) (toList (fmap g sp))
>   s3  = ( map g' aps )
>       ={ Refl }=
>         ( map ((uncurry (*)) . (cross g id)) aps )
>       ={ sym (mapFusion (uncurry (*)) (cross g id) aps) }=
>         ( map (uncurry (*)) (fmap (cross g id) aps) )  
>       ={ cong (sym (toListFmapLemma g sp)) }=
>         ( map (uncurry (*)) (toList (fmap g sp)) )
>       QED
>   s4  : average (map (uncurry (*)) (toList (fmap f sp))) `LTE` average (map g' aps)
>   s4  = replace {P = \ X => average X `LTE` (average (map g' aps))} s2 s1
>   s5  : average (map (uncurry (*)) (toList (fmap f sp))) `LTE` average (map (uncurry (*)) (toList (fmap g sp)))
>   s5  = replace {P = \ X => average (map (uncurry (*)) (toList (fmap f sp))) `LTE` average X} s3 s4
>   s6  : average (fmap f sp) `LTE` average (fmap g sp)
>   s6  = s5

> ||| |expectedValue| is monotone
> monotoneExpectedValue : {A : Type} ->
>                         (f : A -> NonNegDouble) -> (g : A -> NonNegDouble) ->
>                         (p : (a : A) -> f a `LTE` g a) ->
>                         (sp : SimpleProb A) ->
>                         expectedValue (fmap f sp) `LTE` expectedValue (fmap g sp)
> monotoneExpectedValue = monotoneAverage
