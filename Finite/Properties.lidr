> module Finite.Properties

> import Data.Fin
> import Data.Vect
> import Data.Vect.Quantifiers
> import Control.Isomorphism

> import Finite.Predicates
> import Finite.Operations
> import Decidable.Predicates
> import Fin.Operations
> import Fin.Properties
> import Vect.Properties
> import Isomorphism.Operations
> import Isomorphism.Properties
> import Nat.LTProperties
> import Basic.Operations
> import Fun.Properties
> import Sigma.Sigma
> import Pairs.Operations


> %default total

> %access public export


* |Fin n| is finite

> finiteFin : {n : Nat} -> Finite (Fin n)
> finiteFin {n} = MkSigma n isoRefl


* Representations of finite types

> -- toVectComplete : {A : Type} -> (f : Fin n -> A) -> (k : Fin n) -> Elem (f k) (toVect f)


> ||| |toVect| representations of finite types are complete
> toVectComplete : {A : Type} -> (fA : Finite A) -> (a : A) -> Elem a (toVect fA)
> toVectComplete (MkSigma _ iso) a = s3 where
>   s1  :  Elem (from iso (to iso a)) (toVect (from iso))
>   s1  =  toVectComplete (from iso) (to iso a)
>   s2  :  from iso (to iso a) = a
>   s2  =  fromTo iso a
>   s3  :  Elem a (toVect (from iso))
>   s3  =  replace {P = \ z => Elem z (toVect (from iso))} s2 s1
> {-
> toVectComplete fA a = s3 where
>   s1  :  Elem (fromFin fA (toFin fA a)) (toVect fA)
>   s1  =  FinProperties.toVectComplete (fromFin fA) (toFin fA a)
>   s2  :  fromFin fA (toFin fA a) = a
>   s2  =  FromFinToFin fA a
>   s3  :  Elem a (toVect fA)
>   s3  =  replace {P = \ z => Elem z (toVect fA)} s2 s1
> -}
> %freeze toVectComplete -- frozen


> ||| |toVect| representations of finite types are injective
> toVectInjective1 : {A : Type} -> (fA : Finite A) -> Injective1 (toVect fA)
> toVectInjective1 {A} (MkSigma _ iso) i j p = s3 where
>   s1 : index i (toVect (from iso)) = index j (toVect (from iso))
>   s1 = p
>   s2 : (from iso) i = (from iso) j
>   s2 = replace2 {a = A} {a1 = index i (toVect (from iso))} {a2 = (from iso) i}
>                 {b = A} {b1 = index j (toVect (from iso))} {b2 = (from iso) j}
>                 {P = \ a => \b => a = b}
>                 (toVectRepr (from iso) i) (toVectRepr (from iso) j) s1
>   s3 : i = j
>   s3 = injectiveFrom iso i j s2
> %freeze toVectInjective1 -- frozen


* Non empty finite types

> |||
> cardNotZLemma : {A : Type} -> (fA : Finite A) -> A -> CardNotZ fA
> cardNotZLemma fA a = gtZisnotZ (elemLemma {n = card fA} a (toVect fA) (toVectComplete fA a))
> %freeze cardNotZLemma -- frozen


We want to show that, for a finite type |A| and a decidable predicate |P
: A -> Type|, |Exists P| is decidable

< finiteDecLemma : {A : Type} -> {P : A -> Type} -> Finite A -> Dec1 P -> Dec (Exists P)

(See also |finiteDecLemma2| which is a proof without using vectors.)

It is useful to recall (see "VectProperties.lidr") that

< decAny         : {A : Type} -> {P : A -> Type} -> Dec1 P -> Dec1 (Any P)
< AnyExistsLemma : {A : Type} -> {P : A -> Type} -> Any P as -> Exists P
< ElemAnyLemma   : {A : Type} -> {P : A -> Type} -> P a -> Elem a as -> Any P as

With these premises, proving |finiteDecLemma| is almost straightforward:

> finiteDecLemma : {A : Type} -> {P : A -> Type} -> Finite A -> Dec1 P -> Dec (Exists P)
> finiteDecLemma fA dP with (decAny dP (toVect fA))
>   | (Yes prf)   = Yes (AnyExistsLemma prf)
>   | (No contra) = No (\ e => contra (ElemAnyLemma (getProof e) (toVectComplete fA (getWitness e))))
> %freeze finiteDecLemma -- frozen

We pattern match on |decAny dP (toVect fA)|: the result is either a |prf
: Any P (toVect fA)| or a function |contra : Any P (toVect fA) ->
Void|. In the first case we just apply |AnyExistsLemma| to |prf|. This
gives us a value of type |Exists P| which is what we need. In the second
case we have to implement a function of type |Exists P -> Void|. We do
this by applying |contra|. To this end, we need a value of type |Any P
(toVect fA)|. We compute a value of type |Any P (toVect fA)| by applying
|ElemAnyLemma|.

> finiteDecSigmaLemma : {A : Type} -> {P : A -> Type} -> Finite A -> ((a : A) -> Dec (P a)) -> Dec (Sigma A P)
> finiteDecSigmaLemma fA dP with (decAny dP (toVect fA))
>   | (Yes prf)   = Yes (AnySigmaLemma prf)
>   | (No contra) = No (\ e => contra (ElemAnyLemma (getProof e) (toVectComplete fA (getWitness e))))


* Finiteness of products

> ||| If |P| and |Q| are finite, |(P , Q)| is finite
> finiteProduct : {A, B : Type} -> Finite A -> Finite B -> Finite (A, B)
> -- finiteProduct {A} {B} (Evidence m isoA) (Evidence n isoB) =
> --   Evidence (m * n) (isoTrans (pairCong isoA isoB) finPairTimes)
> finiteProduct {A} {B} (MkSigma _ isoA) (MkSigma _ isoB) =
>   MkSigma _ (isoTrans (pairCong isoA isoB) finPairTimes)
> %freeze finiteProduct -- frozen


> finitePair : {A, B : Type} -> Finite A -> Finite B -> Finite (A, B)
> finitePair = finiteProduct
> %freeze finitePair -- frozen


> {- we have to comply with the new |record| syntax for this to type check

----

Porting the proof from the Vect world to the Finite world.

Pseudo-code: case on the size |n| of the finite set
0: empty set => No
(n+1): case P (A 0) of
         Yes -> Yes
         No  -> recursive call with slightly smaller Finite

Some helpers needed to map between Dec's etc.
In fact, Iso is not needed - we can map already with just any pair of functions:

> decIso' : {X : Type} -> {Y : Type} -> (to : X -> Y) -> (from : Y -> X) -> Dec X -> Dec Y
> decIso' to from (Yes x) = Yes (to x)
> decIso' to from (No nx) = No (nx . from)

> decIso : {X : Type} -> {Y : Type} -> Iso X Y -> Dec X -> Dec Y
> decIso (MkIso to from _ _) = decIso' to from

This |lemma| is roughly where we want to end up:

< lemma : (n : Nat) -> {A : Type} -> FiniteN n A -> {P : A -> Type} -> Dec1 P -> Dec (Exists P)

But let's start with a simpler version, ignoring A for now:

< decExistsFin : (n : Nat) -> (P : Fin n -> Type) -> (dP : Dec1 P) -> Dec (Exists P)

Dec (Exists P) is either Yes (an index (i : Fin n) and a proof (p : P
i)) or No (a function showing that any such "index+proof-pair" is
absurd). To show that, we compute the lowest index for which we get a
Yes, or No if no such index exists.

A predicate over |Fin n| can be seen as a vector, so we use the
helper function |tail| from FinOperations.lidr:

< tail : {A : Type} -> (Fin (S n) -> A) -> (Fin n -> A)
< tail P = P . FS

Similarly |Dec1| over |Fin n| can be seen as a vector of decidability
tests. Thus we also need a |Dec1|-version of tail:

> tailDec1 : {n : Nat} -> {P : Fin (S n) -> Type} -> Dec1 P -> Dec1 (tail P)
> tailDec1 dP = \x => dP (FS x)

REMARK{Nicola}{"tail restrictions of decidable predicates are
decidable". This should hold for no matter what restriction, in
fact. But we do not have a notion of subtype already and therefore we do
not have a notion of restriction.}

Next we define the base- and step-case for decidability of predicates
over |Fin n|:

> decNil : {P : Fin 0 -> Type} -> Dec (Exists P)
> decNil = No (\(Evidence wit pro)=> FinZElim wit)

We defined |decCons| to combine decidability tests for the "head" and
the "tail" of a predicate |P| into decidability for the full
predicate. (Pick the lowest index with a |Yes|.)

> using (n : Nat, P : Fin (S n) -> Type)
>   exiCons  :                    Exists (tail P)  ->      Exists P
>   exiCons (Evidence i p) = Evidence (FS i) p

>   nExiCons : Not (P FZ) -> Not (Exists (tail P)) -> Not (Exists P)
>   nExiCons n0 nt (Evidence FZ      p) = n0 p
>   nExiCons n0 nt (Evidence (FS i)  p) = nt (Evidence i p)

>   decCons  : Dec (P FZ) -> Dec (Exists (tail P)) -> Dec (Exists P)
>   decCons (Yes p) _        = Yes (Evidence FZ p)
>   decCons (No np) (Yes pt) = Yes (exiCons pt)
>   decCons (No np) (No npt) = No  (nExiCons np npt)

Find the lowest index for which |dP| says |Yes|.

> decExistsFin : (n : Nat) -> (P : Fin n -> Type) -> Dec1 P -> Dec (Exists P)
> decExistsFin Z     P dP = decNil
> decExistsFin (S n) P dP = decCons (dP FZ) (decExistsFin n (tail P)
>                                                           (tailDec1 dP))

With the simpler case out of the way we can return to the more general case:

> existsIsoTo : {X : Type} -> {Y : Type} ->
>             (iso : Iso X Y) -> (P : X -> Type) ->
>             Exists (P . (from iso)) -> Exists P
> existsIsoTo {X} {Y} iso P (Evidence y pf) = Evidence (from iso y) pf

> existsIsoFrom : {X : Type} -> {Y : Type} ->
>             (iso : Iso X Y) -> (P : X -> Type) ->
>             Exists P -> Exists (P . (from iso))
> existsIsoFrom {X} {Y} iso P (Evidence x pf) = Evidence (to iso x) pf'
>   where
>     pf' : P (from iso (to iso x))
>     pf' = replace (sym (fromTo iso x)) pf

This is the core result:

> finiteDecHelper : (n : Nat) -> {A : Type} -> FiniteN n A ->
>                   (P : A -> Type) -> Dec1 P -> Dec (Exists P)
> finiteDecHelper n iso P dP = decIso' (existsIsoTo   iso P)
>                                      (existsIsoFrom iso P)
>                                      (decExistsFin n  (P . (from iso))
>                                                       (\x => dP (from iso x)))

which can be packaged up as what we aimed for at the beginning:

> finiteDecLemma2 : {A : Type} -> {P : A -> Type} ->
>                   Finitea2 {P} (Evidence n iso) dP = finiteDecHelper n iso P dP

> ---}
