> module FastSimpleProb.MonadicOperations

> import Data.List
> import Data.List.Quantifiers
> import Data.So

> import FastSimpleProb.SimpleProb
> import FastSimpleProb.BasicOperations
> import FastSimpleProb.BasicProperties
> import Double.Predicates
> import NonNegDouble.NonNegDouble
> import NonNegDouble.Postulates
> import NonNegDouble.Constants
> import NonNegDouble.BasicOperations
> import NonNegDouble.BasicProperties
> import List.Operations
> import List.Properties
> import Fun.Operations
> import Sigma.Sigma

> %default total
> %access public export
> %auto_implicits off


* |SimpleProb| is a functor:

> |||
> fmap : {A, B : Type} -> (A -> B) -> SimpleProb A -> SimpleProb B
> fmap f (MkSimpleProb aps psum) = MkSimpleProb aps' psum' where
>   aps'  : List (B, NonNegDouble)
>   aps'  = map (cross f id) aps
>   psum' : Positive (toDouble (sumMapSnd aps'))
>   psum' = replace {P = \ X => Positive (toDouble X)} s2 psum where
>     s1 : map snd (map (cross f id) aps) = map snd aps
>     s1 = mapSndMapCrossAnyIdLemma f aps
>     s2 : sumMapSnd aps = sumMapSnd aps'
>     s2 = cong {f = sum} (sym s1)


* |SimpleProb| is a monad:

> |||
> ret : {A : Type} -> A -> SimpleProb A
> ret a = MkSimpleProb [(a, one)] positiveOne


> |||
> bind : {A, B : Type} -> SimpleProb A -> (A -> SimpleProb B) -> SimpleProb B
> bind {A} {B} (MkSimpleProb aps psum) f = normalize (MkSimpleProb bps' psum') where
>   f' : A -> List (B, NonNegDouble)
>   f' a = toList (normalize (f a))
>   psums' : (a : A) -> Positive (toDouble (sumMapSnd (f' a)))
>   psums' a = toListLemma (normalize (f a))
>   bps' : List (B, NonNegDouble)
>   bps' = mvMult aps f'  
>   psum' : Positive (toDouble (sumMapSnd bps'))
>   psum' = mvMultLemma aps psum f' psums'


* |SimpleProb| is a container monad:

> |||
> Elem : {A : Type} -> A -> SimpleProb A -> Type
> Elem a sp = Elem a (support sp)

> |||
> NonEmpty : {A : Type} -> SimpleProb A -> Type
> NonEmpty sp = List.Operations.NonEmpty (support sp) 

> |||
> All : {A : Type} -> (P : A -> Type) -> SimpleProb A -> Type
> All P sp = All P (support sp) 

> ||| Tagging
> tagElem  :  {A : Type} -> (sp : SimpleProb A) -> SimpleProb (Sigma A (\ a => a `Elem` sp))
> tagElem sp = MkSimpleProb aps' psum' where
>     ssp  : List A
>     ssp  = support sp
>     wsp  : List NonNegDouble
>     wsp  = weights sp
>     as'  : List (Sigma A (\ a => a `Elem` sp))
>     as'  = List.Operations.tagElem ssp
>     aps' : List (Sigma A (\ a => a `Elem` sp), NonNegDouble)
>     aps' = zip as' wsp
>     psum' : Positive (toDouble (sumMapSnd aps'))
>     psum' = s9 where
>       s1 : sumMapSnd aps' = sum (snd (unzip aps'))
>       s1 = sumMapSndUnzipLemma aps'
>       s2 : length as' = length ssp
>       s2 = tagElemPreservesLength ssp
>       s3 : length ssp = length wsp
>       s3 = lengthSupportWeightsLemma sp
>       s4 : length as' = length wsp
>       s4 = trans s2 s3
>       s5 : unzip (zip as' wsp) = (as', wsp)
>       s5 = unzipZipLemma as' wsp s4
>       s6 : snd (unzip aps') = wsp
>       s6 = cong {f = snd} s5
>       s7 : Positive (toDouble (sum wsp))
>       s7 = positiveWeights sp
>       s8 : Positive (toDouble (sum (snd (unzip aps'))))
>       s8 = replace {P = \ X => Positive (toDouble (sum X))} (sym s6) s7
>       s9 : Positive (toDouble (sumMapSnd aps'))
>       s9 = replace {P = \ X => Positive (toDouble X)} (sym s1) s8


> {-

> ---}
 
