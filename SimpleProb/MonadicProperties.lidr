> module SimpleProb.MonadicProperties

> import Data.List
> import Data.List.Quantifiers
> import Syntax.PreorderReasoning

> import SimpleProb.SimpleProb
> import SimpleProb.BasicOperations
> import SimpleProb.BasicProperties
> import SimpleProb.MonadicOperations
> import NonNegRational.NonNegRational
> import NonNegRational.BasicOperations
> import NonNegRational.BasicProperties

> import Nat.Positive
> import Nat.Coprime
> import Fraction.Normal
> import Num.Refinements
> import Num.Properties
> import Fun.Operations
> import List.Operations
> import List.Properties
> import Unique.Predicates
> import Finite.Predicates
> import Sigma.Sigma

> %default total
> %access public export
> -- %access export
> %auto_implicits off


* Properties of |normalize|, |support| and |ret|:

> |||
> normalizeRetLemma : {A : Type} -> (a : A) -> normalize (ret a) = ret a
> normalizeRetLemma a = ( normalize (ret a) )
>                     ={ Refl }=
>                       ( normalize (MkSimpleProb ((a, 1) :: Nil) (sumMapSndSingletonLemma a 1)) )
>                     ={ Refl }=
>                       ( MkSimpleProb ((a, 1) :: Nil) (sumMapSndSingletonLemma a 1) ) 
>                     ={ Refl }=  
>                       ( ret a )
>                     QED
> {-
> normalizeRetLemma a = s9 where
>   s1 : normalize (ret a) = normalize (MkSimpleProb ((a, 1) :: Nil) (sumMapSndSingletonLemma a 1))
>   s1 = Refl
>   s2 : normalize (MkSimpleProb ((a, 1) :: Nil) (sumMapSndSingletonLemma a 1))
>        =
>        MkSimpleProb (discardBySndZero ((a, 1) :: Nil)) 
>                     (trans (discardBySndZeroLemma ((a, 1) :: Nil)) (sumMapSndSingletonLemma a 1))
>   s2 = Refl                  
>   s3 : discardBySndZero ((a, 1) :: Nil) = (a, 1) :: Nil
>   s3 = discardBySndZeroLemma1 a 1 ?oneNotZero
>   s4 : discardBySndZeroLemma ((a, 1) :: Nil) = Refl {} {} {}
>   s4 = ?lika
>   s5 : MkSimpleProb (discardBySndZero ((a, 1) :: Nil)) 
>                     (trans (discardBySndZeroLemma ((a, 1) :: Nil)) (sumMapSndSingletonLemma a 1))
>        =
>        MkSimpleProb ((a, 1) :: Nil) (trans Refl (sumMapSndSingletonLemma a 1))
>   s5 = ?leka
>   s6 : MkSimpleProb ((a, 1) :: Nil) (trans Refl (sumMapSndSingletonLemma a 1))
>        = 
>        MkSimpleProb ((a, 1) :: Nil) (sumMapSndSingletonLemma a 1)
>   s6 = Refl
>   s7 : MkSimpleProb ((a, 1) :: Nil) (sumMapSndSingletonLemma a 1) = ret a
>   s7 = Refl
>   s9 : normalize (ret a) = ret a
>   s9 = trans s1 (trans s2 (trans s5 (trans s6 s7)))
> -}

> |||
> supportRetLemma : {A : Type} -> 
>                   (a : A) -> support (SimpleProb.MonadicOperations.ret a) = List.Operations.ret a
> supportRetLemma a = ( support (SimpleProb.MonadicOperations.ret a) )
>                   ={ Refl }=
>                     ( map fst (toList (normalize (SimpleProb.MonadicOperations.ret a))) )
>                   ={ cong {f = \ X => map Prelude.Basics.fst (toList X)} (normalizeRetLemma a) }=
>                     ( map fst (toList (SimpleProb.MonadicOperations.ret a)) )
>                   ={ Refl }=
>                     ( map fst (toList (MkSimpleProb ((a, 1) :: Nil) (sumMapSndSingletonLemma a 1))) )
>                   ={ Refl }=
>                     ( map fst ((a, 1) :: Nil) )  
>                   ={ Refl }=
>                     ( a :: Nil )  
>                   ={ Refl }=
>                     ( List.Operations.ret a )
>                   QED 


* |SimpleProb| is a container monad:

> |||
> elemNonEmptySpec0 : {A : Type} ->
>                     (a : A) -> (sp : SimpleProb A) ->
>                     a `Elem` sp -> SimpleProb.MonadicOperations.NonEmpty sp
> elemNonEmptySpec0 {A} a sp aesp = List.Properties.elemNonEmptySpec0 a (support sp) aesp

> |||
> elemNonEmptySpec1 : {A : Type} ->
>                     (sp : SimpleProb A) ->
>                     SimpleProb.MonadicOperations.NonEmpty sp -> Sigma A (\ a => a `Elem` sp)
> elemNonEmptySpec1 {A} sp nesp = List.Properties.elemNonEmptySpec1 (support sp) nesp

> |||
> containerMonadSpec1 : {A : Type} -> {a : A} -> a `SimpleProb.MonadicOperations.Elem` (ret a)
> containerMonadSpec1 {A} {a} = s3 where
>   s1 : a `Data.List.Elem` (List.Operations.ret a)
>   s1 = List.Properties.containerMonadSpec1
>   s2 : a `Data.List.Elem` (support (SimpleProb.MonadicOperations.ret a))
>   s2 = replace {P = \ X => a `Data.List.Elem` X} (sym (supportRetLemma a)) s1
>   s3 : a `SimpleProb.MonadicOperations.Elem` (ret a)
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
> finiteNonEmpty : {A : Type} -> (sp : SimpleProb A) -> Finite (SimpleProb.MonadicOperations.NonEmpty sp)
> finiteNonEmpty sp = List.Properties.finiteNonEmpty (support sp)

> ||| NotEmpty is decidable
> decidableNonEmpty : {A : Type} -> (sp : SimpleProb A) -> Dec (SimpleProb.MonadicOperations.NonEmpty sp)
> decidableNonEmpty sp = List.Properties.decidableNonEmpty (support sp)

* |SimpleProb|s are never empty

> |||
> nonEmptyLemma1 : {A : Type} -> (sp : SimpleProb A) -> List.Operations.NonEmpty (toList sp)
> nonEmptyLemma1 {A} (MkSimpleProb Nil s1p) = void s9 where
>   s1 : sumMapSnd {A = A} {B = NonNegRational} Nil = 0
>   s1 = sumMapSndNilLemma {A = A} {B = NonNegRational}
>   s2 : sumMapSnd {A = A} {B = NonNegRational} Nil = 1
>   s2 = s1p
>   s3 : (=) {A = NonNegRational} {B = NonNegRational} 1 0
>   s3 = trans (sym s2) s1
>   s9 : Void
>   s9 = not1Eq0 s3
> nonEmptyLemma1 (MkSimpleProb (ap :: aps) s1p) = () 

> |||
> nonEmptyLemma : {A : Type} -> (sp : SimpleProb A) -> NonEmpty sp
> nonEmptyLemma {A} sp = s4 where
>   s1 : List.Operations.NonEmpty (toList (normalize sp))
>   s1 = nonEmptyLemma1 (normalize sp)
>   s2 : List.Operations.NonEmpty (map fst (toList (normalize sp)))
>   s2 = mapPreservesNonEmpty fst (toList (normalize sp)) s1
>   s3 : List.Operations.NonEmpty (support sp) 
>   s3 = s2
>   s4 : NonEmpty sp
>   s4 = s3


> |||
> toListFmapLemma : {A, B : Type} -> 
>                   (f : A -> B) -> (sp : SimpleProb A) ->
>                   toList (fmap f sp) = fmap (cross f id) (toList sp)
> toListFmapLemma f (MkSimpleProb aps s1p) = 
>     ( toList (fmap f (MkSimpleProb aps s1p)) )
>   ={ Refl }=
>     ( toList (MkSimpleProb 
>               (fmap (cross f id) aps) 
>               (trans Refl (trans (cong (mapSndMapCrossAnyIdLemma f aps)) s1p))) )
>   ={ Refl }=  
>     ( fmap (cross f id) aps )
>   ={ Refl }=
>     ( fmap (cross f id) (toList (MkSimpleProb aps s1p)) )
>   QED


> {-

> ---}
