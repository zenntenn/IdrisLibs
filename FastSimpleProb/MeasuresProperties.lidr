> module FastSimpleProb.MeasuresProperties

> import Data.So
> import Syntax.PreorderReasoning

> import FastSimpleProb.SimpleProb
> import FastSimpleProb.BasicOperations
> import FastSimpleProb.MonadicOperations
> import FastSimpleProb.MonadicPostulates
> import FastSimpleProb.MonadicProperties
> import FastSimpleProb.Predicates
> import FastSimpleProb.Functor
> import FastSimpleProb.Measures
> import Double.Predicates
> import NonNegDouble.NonNegDouble
> import NonNegDouble.Predicates
> import NonNegDouble.BasicOperations
> import NonNegDouble.Operations
> import NonNegDouble.Properties
> import NonNegDouble.Measures
> import NonNegDouble.LTEProperties
> import List.Operations
> import List.Properties
> import Fun.Operations
> import Rel.TotalPreorder
> import Pairs.Operations
> import Functor.Predicates
> import Functor.Properties

> %default total
> %access public export
> %auto_implicits off


* Monotonicity (of |SimpleProb| measures):

> ||| Monotonicity
> Monotone : (SimpleProb NonNegDouble -> NonNegDouble) -> Type
> Monotone = Functor.Predicates.Monotone {B = NonNegDouble} {C = NonNegDouble} {F = SimpleProb} LTE LTE 



* General monotonicity results

> ||| |monotoneNaturalLemma| for |SimpleProb|s
> normalizePreservesMonotonicity : (m : SimpleProb NonNegDouble -> NonNegDouble) -> 
>                                  Monotone m -> 
>                                  Monotone (m . normalize)
> normalizePreservesMonotonicity m mm = 
>   monotoneNaturalLemma {B = NonNegDouble} {C = NonNegDouble} {F = SimpleProb} 
>                        LTE LTE m mm normalize naturalNormalize


* Monotonicity of measures

> using implementation NumNonNegDouble
>   ||| |(uncurry (*)) . (cross f id)| is monotone
>   monotoneUncurryMultCrossId : {A : Type} ->
>                                (f : A -> NonNegDouble) -> (g : A -> NonNegDouble) ->
>                                (p : (a : A) -> f a `LTE` g a) ->
>                                (ap : (A, NonNegDouble)) ->
>                                uncurry (*) ((cross f id) ap) `LTE` uncurry (*) ((cross g id) ap)
>   monotoneUncurryMultCrossId {A} f g p (a, x) = s3 where
>     s1 : f a `LTE` g a
>     s1 = p a
>     s2 : (f a) * x `LTE` (g a) * x
>     s2 = monotoneMultLTE s1 (reflexiveLTE x)
>     s3 : uncurry (*) ((cross f id) (a, x)) `LTE` uncurry (*) ((cross g id) (a, x))
>     s3 = s2

> using implementation NumNonNegDouble
>   ||| |sum| is monotone
>   monotoneSum : Monotone sum
>   monotoneSum = ms where
>     ms  : {A : Type} ->
>           (f : A -> NonNegDouble) -> 
>           (g : A -> NonNegDouble) -> 
>           (p : (a : A) -> f a `LTE` g a) -> 
>           (sp : SimpleProb A) -> 
>           sum (map f sp) `LTE` sum (map g sp)
>     ms {A} f g p sp = s6 where        
>       f'  : (A, NonNegDouble) -> NonNegDouble
>       f'  = uncurry (*) . (cross f id)
>       g'  : (A, NonNegDouble) -> NonNegDouble
>       g'  = uncurry (*) . (cross g id)
>       p'  : (ap : (A, NonNegDouble)) -> f' ap `LTE` g' ap
>       p'  = monotoneUncurryMultCrossId f g p 
>       aps : List (A, NonNegDouble)
>       aps = toList sp
>       s1  : Prelude.Foldable.sum (map f' aps) `LTE` Prelude.Foldable.sum (map g' aps)
>       s1  = monotoneSum {A = (A, NonNegDouble)} f' g' p' aps 
>       s2  : map f' aps = map (uncurry (*)) (toList (fmap f sp))
>       s2  = ( map f' aps )
>           ={ Refl }=
>             ( map ((uncurry (*)) . (cross f id)) aps )
>           ={ sym (mapFusion (uncurry (*)) (cross f id) aps) }=
>             ( map (uncurry (*)) (fmap (cross f id) aps) )  
>           ={ cong (sym (toListFmapLemma f sp)) }=
>             ( map (uncurry (*)) (toList (fmap f sp)) )
>           QED
>       s3  : map g' aps = map (uncurry (*)) (toList (fmap g sp))
>       s3  = ( map g' aps )
>           ={ Refl }=
>             ( map ((uncurry (*)) . (cross g id)) aps )
>           ={ sym (mapFusion (uncurry (*)) (cross g id) aps) }=
>             ( map (uncurry (*)) (fmap (cross g id) aps) )  
>           ={ cong (sym (toListFmapLemma g sp)) }=
>            ( map (uncurry (*)) (toList (fmap g sp)) )
>           QED
>       s4  : Prelude.Foldable.sum (map (uncurry (*)) (toList (fmap f sp))) `LTE` Prelude.Foldable.sum (map g' aps)
>       s4  = replace {P = \ X => Prelude.Foldable.sum X `LTE` (Prelude.Foldable.sum (map g' aps))} s2 s1
>       s5  : Prelude.Foldable.sum (map (uncurry (*)) (toList (fmap f sp))) `LTE` Prelude.Foldable.sum (map (uncurry (*)) (toList (fmap g sp)))
>       s5  = replace {P = \ X => Prelude.Foldable.sum (map (uncurry (*)) (toList (fmap f sp))) `LTE` Prelude.Foldable.sum X} s3 s4
>       s6  : sum (fmap f sp) `LTE` sum (fmap g sp)
>       s6  = s5

> ||| |expectedValue| is monotone
> monotoneExpectedValue : Monotone expectedValue
> monotoneExpectedValue = normalizePreservesMonotonicity sum monotoneSum


> {-


> ---}
