> module SimpleProb.Measures

> import Syntax.PreorderReasoning

> import SimpleProb.SimpleProb
> import SimpleProb.BasicOperations
> import SimpleProb.MonadicOperations
> import SimpleProb.MonadicProperties
> import NonNegRational.NonNegRational
> import NonNegRational.BasicOperations
> import NonNegRational.BasicProperties
> import NonNegRational.Measures
> import NonNegRational.MeasureProperties
> import NonNegRational.LTEProperties
> import Nat.Positive
> import Fraction.Normal
> import List.Operations
> import List.Properties
> import Fun.Operations

> import NonNegRational.Predicates

> %default total
> %access public export
> %auto_implicits off


* Measures

> ||| Expected value
> expectedValue : SimpleProb NonNegRational -> NonNegRational
> expectedValue = Prelude.Foldable.sum . (map (uncurry (*))) . toList


* Monotonicity of measures

> |||
> monotoneUncurryMultCrossId : {A : Type} ->
>                              (f : A -> NonNegRational) -> (g : A -> NonNegRational) ->
>                              (p : (a : A) -> f a `LTE` g a) ->
>                              (ap : (A, NonNegRational)) ->
>                              uncurry (*) ((cross f id) ap) `LTE` uncurry (*) ((cross g id) ap)
> monotoneUncurryMultCrossId {A} f g p (a, x) = s3 where
>   s1 : f a `LTE` g a
>   s1 = p a
>   s2 : (f a) * x `LTE` (g a) * x
>   s2 = monotoneMultLTE s1 (reflexiveLTE x)
>   s3 : uncurry (*) ((cross f id) (a, x)) `LTE` uncurry (*) ((cross g id) (a, x))
>   s3 = s2

> monotoneExpectedValue : {A : Type} ->
>                         (f : A -> NonNegRational) -> (g : A -> NonNegRational) ->
>                         (p : (a : A) -> f a `LTE` g a) ->
>                         (as : SimpleProb A) ->
>                         expectedValue (fmap f as) `LTE` expectedValue (fmap g as) 
> monotoneExpectedValue {A} f g p sp = s6 where
>   f'  : (A, NonNegRational) -> NonNegRational
>   f'  = uncurry (*) . (cross f id)
>   g'  : (A, NonNegRational) -> NonNegRational
>   g'  = uncurry (*) . (cross g id)
>   p'  : (ap : (A, NonNegRational)) -> f' ap `LTE` g' ap
>   p'  = monotoneUncurryMultCrossId f g p 
>   aps : List (A, NonNegRational)
>   aps = toList sp
>   s1  : Prelude.Foldable.sum (map f' aps) `LTE` Prelude.Foldable.sum (map g' aps)
>   s1  = monotoneSum {A = (A, NonNegRational)} f' g' p' aps 
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
>   s4  : Prelude.Foldable.sum (map (uncurry (*)) (toList (fmap f sp))) `LTE` Prelude.Foldable.sum (map g' aps)
>   s4  = replace {P = \ X => Prelude.Foldable.sum X `LTE` (Prelude.Foldable.sum (map g' aps))} s2 s1
>   s5  : Prelude.Foldable.sum (map (uncurry (*)) (toList (fmap f sp))) `LTE` Prelude.Foldable.sum (map (uncurry (*)) (toList (fmap g sp)))
>   s5  = replace {P = \ X => Prelude.Foldable.sum (map (uncurry (*)) (toList (fmap f sp))) `LTE` Prelude.Foldable.sum X} s3 s4
>   s6  : expectedValue (fmap f sp) `LTE` expectedValue (fmap g sp)
>   s6  = s5


