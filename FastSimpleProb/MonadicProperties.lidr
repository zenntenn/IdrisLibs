> module FastSimpleProb.MonadicProperties

> import Data.List
> import Data.List.Quantifiers
> import Syntax.PreorderReasoning

> import FastSimpleProb.SimpleProb
> import FastSimpleProb.BasicOperations
> import FastSimpleProb.BasicProperties
> import FastSimpleProb.MonadicOperations
> import FastSimpleProb.Predicates
> -- import FastSimpleProb.MonadicPostulates
> import NonNegDouble.NonNegDouble
> import NonNegDouble.Postulates
> import NonNegDouble.Constants
> import NonNegDouble.BasicOperations
> import NonNegDouble.BasicProperties

> import Double.Predicates
> import Num.Refinements
> import Num.Properties
> import Fun.Operations
> import List.Operations
> import List.Properties
> import Unique.Predicates
> import Finite.Predicates
> import Sigma.Sigma
> import Pairs.Operations

> %default total
> %access public export
> -- %access export
> %auto_implicits off


* Properties of |support| and |ret|:

> |||
> supportRetLemma : {A : Type} -> 
>                   (a : A) -> support (ret a) = ret a
> supportRetLemma a = ( support (ret a) )
>                   ={ Refl }=
>                     ( map fst (toList (ret a)) )
>                   ={ Refl }=
>                     ( map fst (toList (MkSimpleProb [(a, one)] positiveOne)) )
>                   ={ Refl }=
>                     ( map fst [(a, one)] )  
>                   ={ Refl }=
>                     ( [a] )  
>                   ={ Refl }=
>                     ( ret a )
>                   QED 


* |SimpleProb| is a container monad:

> |||
> elemNonEmptySpec0 : {A : Type} ->
>                     (a : A) -> (sp : SimpleProb A) -> a `Elem` sp -> NonEmpty sp
> elemNonEmptySpec0 {A} a sp aesp = List.Properties.elemNonEmptySpec0 a (support sp) aesp

> |||
> elemNonEmptySpec1 : {A : Type} ->
>                     (sp : SimpleProb A) -> NonEmpty sp -> Sigma A (\ a => a `Elem` sp)
> elemNonEmptySpec1 {A} sp nesp = List.Properties.elemNonEmptySpec1 (support sp) nesp

> |||
> containerMonadSpec1 : {A : Type} -> {a : A} -> a `FastSimpleProb.MonadicOperations.Elem` (ret a)
> containerMonadSpec1 {A} {a} = s3 where
>   s1 : a `Data.List.Elem` (List.Operations.ret a)
>   s1 = List.Properties.containerMonadSpec1
>   s2 : a `Data.List.Elem` (support (FastSimpleProb.MonadicOperations.ret a))
>   s2 = replace {P = \ X => a `Data.List.Elem` X} (sym (supportRetLemma a)) s1
>   s3 : a `FastSimpleProb.MonadicOperations.Elem` (ret a)
>   s3 = s2

> |||
> containerMonadSpec3 : {A : Type} -> {P : A -> Type} ->
>                       (a : A) -> (sp : SimpleProb A) ->
>                       All P sp -> a `Elem` sp -> P a
> containerMonadSpec3 {A} {P} a sp allp elemp = List.Properties.containerMonadSpec3 a (support sp) allp elemp


* Specific container monad properties

> |||
> uniqueAllLemma : {A : Type} -> {P : A -> Type} -> 
>                  Unique1 P -> (sp : SimpleProb A) -> Unique (All P sp)
> uniqueAllLemma u1P sp = List.Properties.uniqueAllLemma u1P (support sp)

> |||
> finiteAll : {A : Type} -> {P : A -> Type} -> 
>             Finite1 P -> (sp : SimpleProb A) -> Finite (All P sp)
> finiteAll f1P sp = List.Properties.finiteAll f1P (support sp)

> ||| All is decidable
> decidableAll : {A : Type} -> {P : A -> Type} -> 
>                (dec : (a : A) -> Dec (P a)) -> (sp : SimpleProb A) -> Dec (All P sp)
> decidableAll dec sp = List.Properties.decidableAll dec (support sp)

> ||| NotEmpty is finite
> finiteNonEmpty : {A : Type} -> (sp : SimpleProb A) -> Finite (FastSimpleProb.MonadicOperations.NonEmpty sp)
> finiteNonEmpty sp = List.Properties.finiteNonEmpty (support sp)

> ||| NotEmpty is decidable
> decidableNonEmpty : {A : Type} -> (sp : SimpleProb A) -> Dec (FastSimpleProb.MonadicOperations.NonEmpty sp)
> decidableNonEmpty sp = List.Properties.decidableNonEmpty (support sp)


* |SimpleProb|s are never empty

> |||
> nonEmptyLemma1 : {A : Type} -> (sp : SimpleProb A) -> List.Operations.NonEmpty (toList sp)
> nonEmptyLemma1 {A} (MkSimpleProb Nil psum) = s4 where
>   s1 : sumMapSnd {A = A} {B = NonNegDouble} Nil = zero
>   s1 = sumMapSndNilLemma {A = A} {B = NonNegDouble}
>   s2 : Positive (toDouble (sumMapSnd {A = A} {B = NonNegDouble} Nil))
>   s2 = psum
>   s3 : Positive (toDouble zero)
>   s3 = replace {P = \ X => Positive (toDouble X)} s1 s2 
>   s4 : List.Operations.NonEmpty {A = (A, NonNegDouble)} (toList (MkSimpleProb Nil psum))
>   s4 = notPositiveZero s3
> nonEmptyLemma1 (MkSimpleProb (ap :: aps) psum) = () 

> |||
> nonEmptyLemma : {A : Type} -> (sp : SimpleProb A) -> NonEmpty sp
> nonEmptyLemma {A} sp = s4 where
>   s1 : List.Operations.NonEmpty (toList sp)
>   s1 = nonEmptyLemma1 sp
>   s2 : List.Operations.NonEmpty (map fst (toList sp))
>   s2 = mapPreservesNonEmpty fst (toList sp) s1
>   s3 : List.Operations.NonEmpty (support sp) 
>   s3 = s2
>   s4 : NonEmpty sp
>   s4 = s3


* Properies of |fmap| and |toList|

> |||
> toListFmapLemma : {A, B : Type} -> 
>                   (f : A -> B) -> (sp : SimpleProb A) ->
>                   toList (fmap f sp) = fmap (cross f id) (toList sp)
> toListFmapLemma f (MkSimpleProb aps psum) = 
>     ( toList (fmap f (MkSimpleProb aps psum)) )
>   ={ Refl }=
>     ( toList (MkSimpleProb 
>               (fmap (cross f id) aps) 
>               (replace {P = \ X => Positive (toDouble X)} (cong {f = sum} (sym (mapSndMapCrossAnyIdLemma f aps))) psum)) )
>   ={ Refl }=  
>     ( fmap (cross f id) aps )
>   ={ Refl }=
>     ( fmap (cross f id) (toList (MkSimpleProb aps psum)) )
>   QED


> {-

> ---}
