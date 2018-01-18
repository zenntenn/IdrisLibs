> module Chapter02

> import Data.List
> import Data.List.Quantifiers
> import Data.Vect
> import Syntax.PreorderReasoning

> import Enumerated.Enumerated
> import Finite.Predicates
> import Finite.Operations
> import List.Operations
> import List.Properties

> %default total
> %access public export
> %auto_implicits off


* Chapter 2: Concept learning and the general-to-specific ordering


** 2.1 Introduction


** 2.2 A concept learning task


Example: learning the target concept "days on which my friend Aldo
enjoys his favorite water sport"

> data Sky = Sunny | Cloudy | Rainy
>
> implementation Enumerated Sky 3 where
>   values = [Sunny, Cloudy, Rainy]
>   toFin Sunny  = 0
>   toFin Cloudy = 1
>   toFin Rainy  = 2
>   values_match_toFin = Refl
>   
> implementation Eq Sky where
>   x  == y  = toFin x == toFin y

> data AirTemp = Warm | Cold
> 
> implementation Enumerated AirTemp 2 where
>   values = [Warm, Cold]
>   toFin Warm = 0
>   toFin Cold = 1
>   values_match_toFin = Refl
>   
> implementation Eq AirTemp where
>   x  == y  = toFin x == toFin y

> data Humidity = Normal | High
> 
> implementation Enumerated Humidity 2 where
>   values = [Normal, High]
>   toFin Normal = 0
>   toFin High   = 1
>   values_match_toFin = Refl
>   
> implementation Eq Humidity where
>   x  == y  = toFin x == toFin y

> data Wind = Weak | Strong
> 
> implementation Enumerated Wind 2 where
>   values = [Weak, Strong]
>   toFin Weak   = 0
>   toFin Strong = 1
>   values_match_toFin = Refl
>   
> implementation Eq Wind where
>   x  == y  = toFin x == toFin y

> data Water = Cool | Hot
> 
> implementation Enumerated Water 2 where
>   values = [Cool, Hot]
>   toFin Cool = 0
>   toFin Hot  = 1
>   values_match_toFin = Refl
>   
> implementation Eq Water where
>   x  == y  = toFin x == toFin y

> data Forecast = Same | Change
>
> implementation Enumerated Forecast 2 where
>   values = [Same, Change]
>   toFin Same   = 0
>   toFin Change = 1
>   values_match_toFin = Refl
>   
> implementation Eq Forecast where
>   x  == y  = toFin x == toFin y

> EnjoySport : Type
> EnjoySport = Bool

> Day : Type
> Day = (Sky, AirTemp, Humidity, Wind, Water, Forecast)
>
> sky : Day -> Sky
> sky (x, _, _, _, _, _) = x
>
> airTemp : Day -> AirTemp
> airTemp (_, x, _, _, _, _) = x
>
> humidity : Day -> Humidity
> humidity (_, _, x, _, _, _) = x
>
> wind : Day -> Wind
> wind (_, _, _, x, _, _) = x
>
> water : Day -> Water
> water (_, _, _, _, x, _) = x
>
> forecast : Day -> Forecast
> forecast (_, _, _, _, _, x) = x

The task is to learn to predict (approximate) a function 

< c : Day -> EnjoySport

from a set of "training examples". The idea is that a training example
is a pair |(d, b) : (Day, EnjoySport)| with |b = c d| and that the
number of training examples is small in comparison with the size of |Day
-> EnjoySport|. Therefore, the approximation space should also be small
in comparison with the size of |Day -> EnjoySport|.

In the ML parlance, the approximation space is usually called the set of
"hypotheses" (about |c|) or the hypotheses representation. In the
example, we take

> data AnyOrNone = Any | None

> Hypothesis : Type
> Hypothesis = (Either Sky AnyOrNone, 
>               Either AirTemp AnyOrNone, 
>               Either Humidity AnyOrNone, 
>               Either Wind AnyOrNone, 
>               Either Water AnyOrNone, 
>               Either Forecast AnyOrNone)

The interpretation is that the hypothesis

< (Right None, airTemp,    humidity,   wind, water, forecast)

posits |c d = False| independently of |d|. Similarly

< (sky,        Right None, humidity,   wind, water, forecast)
< (sky,        airTemp,    Right None, wind, water, forecast)
< ...

also posit |c d = False| for every |d|. In contrast, the hypothesis

< (Right Any, Right Any, Right Any, Right Any, Right Any, Right Any)

posits that |c d = True| for every |d| and

< (Right Any, Cold, High, Right Any, Right Any, Right Any)

posits that |c d = True| iff |airTemp d = Cold| and |humidity d = High|.
We can implement the interpretation of hypotheses as a function

< fulfils : Day -> Hypothesis -> Bool

that describes if a day fulfills an hypothesis. The implementation of
|fulfils| is tedious but trivial, see Appendix. Among others, |fulfils|
satisfies

< fulfils d (Right Any, Right Any, Right Any, Right Any, Right Any, Right Any) = True

and, as posited above

< fulfils d (Right None, _, _, _, _, _) = False
< fulfils d (_, Right None, _, _, _, _) = False
< fulfils d (_, _, Right None, _, _, _) = False
< fulfils d (_, _, _, Right None, _, _) = False
< fulfils d (_, _, _, _, Right None, _) = False
< fulfils d (_, _, _, _, _, Right None) = False

Under this notion of approximation speace, the task is to find (learn)
an hypothesis |h : Hypothesis| that "best" represents |c| given a set of
training examples.


*** 2.2.1 Notation

We generalize the "enjoy sport" example by introducing generic types for
a set of attributes (instances, with |X = Day| in the example) 

> X : Type

, a set of hypotheses

> H : Type

with an interpretation 

> fulfils : X -> H -> Bool

, a set of examples

> E : Type
> E = (X, Bool)

and the "concept" to be "learned"

> c : X -> Bool

As discussed in the example, the idea is that we are given a training
example

> te : List E 

that represents |c| in the sense that

> teSpec : Type
> teSpec = (e : E) -> e `Elem` te -> c (fst e) = snd e

and we seek an hypothesis 

> h : H 

such that 

> goal : Type
> goal = (x : X) -> fulfils x h = c x


*** 2.2.2 The Inductive Learning Hypothesis

"Any hypothesis found to approximate the target function well over a
sufficiently large set of training examples will also approximate the
target function well over other unobserved examples"


** 2.3 Concept learning as search

In the "enjoy sport" example, |X = Day| and |X| contains 3 * 2^5 = 96
values. |H = Hypothesis| and |H| contains 5 * 4^5 = 5120 values. Notice
that |X -> Bool| contains 2^96 values!

*** 2.3.1 General-to-Specific Ordering of Hypotheses

> LTE : H -> H -> Type
> LTE h1 h2 = (x : X) -> fulfils x h1 = True -> fulfils x h2 = True

|LTE| is a partial order:

> reflexiveLTE : (h : H) -> h `LTE` h
> reflexiveLTE h x p = p

> antisymmetricLTE : (h1 : H) -> (h2 : H) -> h1 `LTE` h2 -> h2 `LTE` h1 -> 
>                    (y : X) -> fulfils y h1 = fulfils y h2 
> antisymmetricLTE h1 h2 p q y with (fulfils y h1) proof prf
>   | True  = ( True )
>           ={ (sym (p y (sym prf))) }=
>             ( fulfils y h2 )
>           QED
>   | False with (fulfils y h2) proof prf'
>       | True  = void (trueNotFalse (sym contra)) where
>           contra : False = True
>           contra = ( False )
>                  ={ prf }=
>                    ( fulfils y h1 )
>                  ={ q y (sym prf') }=
>                    ( True )
>                  QED
>       | False = Refl

> transitiveLTE : (h1, h2, h3 : H) -> h1 `LTE` h2 -> h2 `LTE` h3 -> h1 `LTE` h3
> transitiveLTE h1 h2 h3 p q x fxh1 = q x (p x fxh1)


** 2.4 Find-S: Finding a maximally specific hypothesis

> mostSpecific : H

> mostSpecificSpec : (h : H) -> mostSpecific `LTE` h

> next : (h : H) -> (e : E) -> H

> nextSpec1 : (h : H) -> (e : E) -> snd e = False -> next h e = h

> nextSpec2 : (h : H) -> (e : E) -> snd e = True -> fulfils (fst e) (next h e) = True

> nextSpec3 : (h : H) -> (e : E) -> (h' : H) -> fulfils (fst e) h' = True -> (next h e) `LTE` h'

> findS : List E -> H
> findS      Nil  = mostSpecific
> findS (e :: es) = next (findS es) e


** 2.5 CandidateElimination

*** 2.5.1 Representation

> ClassifiesCorrectly : H -> E -> Type
> ClassifiesCorrectly h e = fulfils (fst e) h = snd e

> decClassifiesCorrectly : (h : H) -> (e : E) -> Dec (ClassifiesCorrectly h e)
> decClassifiesCorrectly h e = decEq (fulfils (fst e) h ) (snd e)

> Consistent : H -> List E -> Type
> Consistent h es = All (ClassifiesCorrectly h) es

> VersionSpace : List E -> Type
> VersionSpace es = Subset H (\ h => Consistent h es)

> decConsistent : (h : H) -> (es : List E) -> Dec (Consistent h es) 
> decConsistent h es = decidableAll (decClassifiesCorrectly h) es

*** 2.5.2 The List-Then_Eliminate Algorithm

> listThenEliminate : Finite H -> (es : List E) -> List (VersionSpace es)
> listThenEliminate fH es = filterTagSubset {A = H} 
>                                           {P = \ h => Consistent h es} 
>                                           (\ h => decConsistent h es)
>                                           (toList (toVect fH))

*** 2.5.3 A more compact Representation for Version Spaces

> Bottom : List E -> H -> Type
> Bottom es h = (Consistent h es, (h' : H) -> Consistent h' es -> h `LTE` h')

> Top : List E -> H -> Type
> Top es h = (Consistent h es, (h' : H) -> Consistent h' es -> h' `LTE` h)

> AboveBottom : List E -> H -> Type
> AboveBottom es h = Exists (\ s => (Bottom es s, s `LTE` h))

> BelowTop : List E -> H -> Type
> BelowTop es h = Exists (\ g => (Top es g, h `LTE` g))

> VersionSpaceRepr : List E -> Type
> VersionSpaceRepr es = Subset H (\ h => (AboveBottom es h, BelowTop es h))

> lemma1 : (es : List E) -> (h : H) -> (AboveBottom es h, BelowTop es h) -> Consistent h es 
> lemma1  Nil      h (ab, bt) = Nil
> lemma1 (e :: es) h (ab, bt) = p :: ps where
>   s  : H
>   s  = getWitness ab
>   s1 : s `LTE`h
>   s1 = snd (getProof ab) 
>   p  : ClassifiesCorrectly h e
>   p  = ?kika
>   ps : All (ClassifiesCorrectly h) es
>   ps = ?kuka


> {-

> lemma2 : (es : List E) -> (h : H) -> Consistent h es -> (AboveBottom es h, BelowTop es h)




* Appendix

> fulfils d (Right None, _, _, _, _, _) = False
> fulfils d (_, Right None, _, _, _, _) = False
> fulfils d (_, _, Right None, _, _, _) = False
> fulfils d (_, _, _, Right None, _, _) = False
> fulfils d (_, _, _, _, Right None, _) = False
> fulfils d (_, _, _, _, _, Right None) = False
>
> fulfils d (Left v1, Left v2, Left v3, Left v4, Left v5, Left v6) =
>   sky d == v1 
>   && 
>   airTemp d == v2 
>   && 
>   humidity d == v3 
>   && 
>   wind d == v4 
>   && 
>   water d == v5 
>   && 
>   forecast d == v6 
>
> fulfils d (Left v1, Left v2, Left v3, Left v4, Left v5, Right Any) =
>   sky d == v1 
>   && 
>   airTemp d == v2 
>   && 
>   humidity d == v3 
>   && 
>   wind d == v4 
>   && 
>   water d == v5
>
> fulfils d (Left v1, Left v2, Left v3, Left v4, Right Any, Left v6) =
>   sky d == v1 
>   && 
>   airTemp d == v2 
>   && 
>   humidity d == v3 
>   && 
>   wind d == v4 
>   && 
>   forecast d == v6 
>
> fulfils d (Left v1, Left v2, Left v3, Left v4, Right Any, Right Any) =
>   sky d == v1 
>   && 
>   airTemp d == v2 
>   && 
>   humidity d == v3 
>   && 
>   wind d == v4 
>
> fulfils d (Left v1, Left v2, Left v3, Right Any, Left v5, Left v6) =
>   sky d == v1 
>   && 
>   airTemp d == v2 
>   && 
>   humidity d == v3 
>   && 
>   water d == v5 
>   && 
>   forecast d == v6 
>
> fulfils d (Left v1, Left v2, Left v3, Right Any, Left v5, Right Any) =
>   sky d == v1 
>   && 
>   airTemp d == v2 
>   && 
>   humidity d == v3 
>   && 
>   water d == v5
>
> fulfils d (Left v1, Left v2, Left v3, Right Any, Right Any, Left v6) =
>   sky d == v1 
>   && 
>   airTemp d == v2 
>   && 
>   humidity d == v3 
>   && 
>   forecast d == v6 
>
> fulfils d (Left v1, Left v2, Left v3, Right Any, Right Any, Right Any) =
>   sky d == v1 
>   && 
>   airTemp d == v2 
>   && 
>   humidity d == v3 
>
> fulfils d (Left v1, Left v2, Right Any, Left v4, Left v5, Left v6) =
>   sky d == v1 
>   && 
>   airTemp d == v2 
>   && 
>   wind d == v4 
>   && 
>   water d == v5 
>   && 
>   forecast d == v6 
>
> fulfils d (Left v1, Left v2, Right Any, Left v4, Left v5, Right Any) =
>   sky d == v1 
>   && 
>   airTemp d == v2 
>   && 
>   wind d == v4 
>   && 
>   water d == v5
>
> fulfils d (Left v1, Left v2, Right Any, Left v4, Right Any, Left v6) =
>   sky d == v1 
>   && 
>   airTemp d == v2 
>   && 
>   wind d == v4 
>   && 
>   forecast d == v6 
>
> fulfils d (Left v1, Left v2, Right Any, Left v4, Right Any, Right Any) =
>   sky d == v1 
>   && 
>   airTemp d == v2 
>   && 
>   wind d == v4 
>
> fulfils d (Left v1, Left v2, Right Any, Right Any, Left v5, Left v6) =
>   sky d == v1 
>   && 
>   airTemp d == v2 
>   && 
>   water d == v5 
>   && 
>   forecast d == v6 
>
> fulfils d (Left v1, Left v2, Right Any, Right Any, Left v5, Right Any) =
>   sky d == v1 
>   && 
>   airTemp d == v2 
>   && 
>   water d == v5
>
> fulfils d (Left v1, Left v2, Right Any, Right Any, Right Any, Left v6) =
>   sky d == v1 
>   && 
>   airTemp d == v2 
>   && 
>   forecast d == v6 
>
> fulfils d (Left v1, Left v2, Right Any, Right Any, Right Any, Right Any) =
>   sky d == v1 
>   && 
>   airTemp d == v2 
>
> fulfils d (Left v1, Right Any, Left v3, Left v4, Left v5, Left v6) =
>   sky d == v1 
>   && 
>   humidity d == v3 
>   && 
>   wind d == v4 
>   && 
>   water d == v5 
>   && 
>   forecast d == v6 
>
> fulfils d (Left v1, Right Any, Left v3, Left v4, Left v5, Right Any) =
>   sky d == v1 
>   && 
>   humidity d == v3 
>   && 
>   wind d == v4 
>   && 
>   water d == v5
>
> fulfils d (Left v1, Right Any, Left v3, Left v4, Right Any, Left v6) =
>   sky d == v1 
>   && 
>   humidity d == v3 
>   && 
>   wind d == v4 
>   && 
>   forecast d == v6 
>
> fulfils d (Left v1, Right Any, Left v3, Left v4, Right Any, Right Any) =
>   sky d == v1 
>   && 
>   humidity d == v3 
>   && 
>   wind d == v4 
>
> fulfils d (Left v1, Right Any, Left v3, Right Any, Left v5, Left v6) =
>   sky d == v1 
>   && 
>   humidity d == v3 
>   && 
>   water d == v5 
>   && 
>   forecast d == v6 
>
> fulfils d (Left v1, Right Any, Left v3, Right Any, Left v5, Right Any) =
>   sky d == v1 
>   && 
>   humidity d == v3 
>   && 
>   water d == v5
>
> fulfils d (Left v1, Right Any, Left v3, Right Any, Right Any, Left v6) =
>   sky d == v1 
>   && 
>   humidity d == v3 
>   && 
>   forecast d == v6 
>
> fulfils d (Left v1, Right Any, Left v3, Right Any, Right Any, Right Any) =
>   sky d == v1 
>   && 
>   humidity d == v3 
>
> fulfils d (Left v1, Right Any, Right Any, Left v4, Left v5, Left v6) =
>   sky d == v1 
>   && 
>   wind d == v4 
>   && 
>   water d == v5 
>   && 
>   forecast d == v6 
>
> fulfils d (Left v1, Right Any, Right Any, Left v4, Left v5, Right Any) =
>   sky d == v1 
>   && 
>   wind d == v4 
>   && 
>   water d == v5
>
> fulfils d (Left v1, Right Any, Right Any, Left v4, Right Any, Left v6) =
>   sky d == v1 
>   && 
>   wind d == v4 
>   && 
>   forecast d == v6 
>
> fulfils d (Left v1, Right Any, Right Any, Left v4, Right Any, Right Any) =
>   sky d == v1 
>   && 
>   wind d == v4 
>
> fulfils d (Left v1, Right Any, Right Any, Right Any, Left v5, Left v6) =
>   sky d == v1 
>   && 
>   water d == v5 
>   && 
>   forecast d == v6 
>
> fulfils d (Left v1, Right Any, Right Any, Right Any, Left v5, Right Any) =
>   sky d == v1 
>   && 
>   water d == v5
>
> fulfils d (Left v1, Right Any, Right Any, Right Any, Right Any, Left v6) =
>   sky d == v1 
>   && 
>   forecast d == v6 
>
> fulfils d (Left v1, Right Any, Right Any, Right Any, Right Any, Right Any) =
>   sky d == v1 
>
> fulfils d (Right Any, Left v2, Left v3, Left v4, Left v5, Left v6) =
>   airTemp d == v2 
>   && 
>   humidity d == v3 
>   && 
>   wind d == v4 
>   && 
>   water d == v5 
>   && 
>   forecast d == v6 
>
> fulfils d (Right Any, Left v2, Left v3, Left v4, Left v5, Right Any) =
>   airTemp d == v2 
>   && 
>   humidity d == v3 
>   && 
>   wind d == v4 
>   && 
>   water d == v5
>
> fulfils d (Right Any, Left v2, Left v3, Left v4, Right Any, Left v6) =
>   airTemp d == v2 
>   && 
>   humidity d == v3 
>   && 
>   wind d == v4 
>   && 
>   forecast d == v6 
>
> fulfils d (Right Any, Left v2, Left v3, Left v4, Right Any, Right Any) =
>   airTemp d == v2 
>   && 
>   humidity d == v3 
>   && 
>   wind d == v4 
>
> fulfils d (Right Any, Left v2, Left v3, Right Any, Left v5, Left v6) =
>   airTemp d == v2 
>   && 
>   humidity d == v3 
>   && 
>   water d == v5 
>   && 
>   forecast d == v6 
>
> fulfils d (Right Any, Left v2, Left v3, Right Any, Left v5, Right Any) =
>   airTemp d == v2 
>   && 
>   humidity d == v3 
>   && 
>   water d == v5
>
> fulfils d (Right Any, Left v2, Left v3, Right Any, Right Any, Left v6) =
>   airTemp d == v2 
>   && 
>   humidity d == v3 
>   && 
>   forecast d == v6 
>
> fulfils d (Right Any, Left v2, Left v3, Right Any, Right Any, Right Any) =
>   airTemp d == v2 
>   && 
>   humidity d == v3 
>
> fulfils d (Right Any, Left v2, Right Any, Left v4, Left v5, Left v6) =
>   airTemp d == v2 
>   && 
>   wind d == v4 
>   && 
>   water d == v5 
>   && 
>   forecast d == v6 
>
> fulfils d (Right Any, Left v2, Right Any, Left v4, Left v5, Right Any) =
>   airTemp d == v2 
>   && 
>   wind d == v4 
>   && 
>   water d == v5
>
> fulfils d (Right Any, Left v2, Right Any, Left v4, Right Any, Left v6) =
>   airTemp d == v2 
>   && 
>   wind d == v4 
>   && 
>   forecast d == v6 
>
> fulfils d (Right Any, Left v2, Right Any, Left v4, Right Any, Right Any) =
>   airTemp d == v2 
>   && 
>   wind d == v4 
>
> fulfils d (Right Any, Left v2, Right Any, Right Any, Left v5, Left v6) =
>   airTemp d == v2 
>   && 
>   water d == v5 
>   && 
>   forecast d == v6 
>
> fulfils d (Right Any, Left v2, Right Any, Right Any, Left v5, Right Any) =
>   airTemp d == v2 
>   && 
>   water d == v5
>
> fulfils d (Right Any, Left v2, Right Any, Right Any, Right Any, Left v6) =
>   airTemp d == v2 
>   && 
>   forecast d == v6 
>
> fulfils d (Right Any, Left v2, Right Any, Right Any, Right Any, Right Any) =
>   airTemp d == v2 
>
> fulfils d (Right Any, Right Any, Left v3, Left v4, Left v5, Left v6) =
>   humidity d == v3 
>   && 
>   wind d == v4 
>   && 
>   water d == v5 
>   && 
>   forecast d == v6 
>
> fulfils d (Right Any, Right Any, Left v3, Left v4, Left v5, Right Any) =
>   humidity d == v3 
>   && 
>   wind d == v4 
>   && 
>   water d == v5
>
> fulfils d (Right Any, Right Any, Left v3, Left v4, Right Any, Left v6) =
>   humidity d == v3 
>   && 
>   wind d == v4 
>   && 
>   forecast d == v6 
>
> fulfils d (Right Any, Right Any, Left v3, Left v4, Right Any, Right Any) =
>   humidity d == v3 
>   && 
>   wind d == v4 
>
> fulfils d (Right Any, Right Any, Left v3, Right Any, Left v5, Left v6) =
>   humidity d == v3 
>   && 
>   water d == v5 
>   && 
>   forecast d == v6 
>
> fulfils d (Right Any, Right Any, Left v3, Right Any, Left v5, Right Any) =
>   humidity d == v3 
>   && 
>   water d == v5
>
> fulfils d (Right Any, Right Any, Left v3, Right Any, Right Any, Left v6) =
>   humidity d == v3 
>   && 
>   forecast d == v6 
>
> fulfils d (Right Any, Right Any, Left v3, Right Any, Right Any, Right Any) =
>   humidity d == v3 
>
> fulfils d (Right Any, Right Any, Right Any, Left v4, Left v5, Left v6) =
>   wind d == v4 
>   && 
>   water d == v5 
>   && 
>   forecast d == v6 
>
> fulfils d (Right Any, Right Any, Right Any, Left v4, Left v5, Right Any) =
>   wind d == v4 
>   && 
>   water d == v5
>
> fulfils d (Right Any, Right Any, Right Any, Left v4, Right Any, Left v6) =
>   wind d == v4 
>   && 
>   forecast d == v6 
>
> fulfils d (Right Any, Right Any, Right Any, Left v4, Right Any, Right Any) =
>   wind d == v4 
>
> fulfils d (Right Any, Right Any, Right Any, Right Any, Left v5, Left v6) =
>   water d == v5 
>   && 
>   forecast d == v6 
>
> fulfils d (Right Any, Right Any, Right Any, Right Any, Left v5, Right Any) =
>   water d == v5
>
> fulfils d (Right Any, Right Any, Right Any, Right Any, Right Any, Left v6) =
>   forecast d == v6 
>
> fulfils d (Right Any, Right Any, Right Any, Right Any, Right Any, Right Any) = True

> ---}


[1] Tom M. Mitchell; "Machine Learning", McGraw-Hill, 1997
 
 
