> module FastSimpleProb.Operations

> import FastSimpleProb.SimpleProb
> import FastSimpleProb.BasicOperations
> import FastSimpleProb.MonadicProperties
> import NonNegDouble.NonNegDouble
> import NonNegDouble.BasicOperations
> import Rel.TotalPreorder
> import NonNegDouble.LTEProperties
> import List.Operations
> import List.Properties
> import Fun.Operations
> import Double.Predicates

> %default total
> %access public export
> %auto_implicits off


> |||
> mostProbableProb : {A : Type} -> (Eq A) => SimpleProb A -> (A, NonNegDouble)
> mostProbableProb {A} sp = argmaxMax totalPreorderLTE aps neaps where
>   aps   : List (A, NonNegDouble)
>   aps   = map (pair (id, (prob sp))) (nub (support sp))
>   nes   : List.Operations.NonEmpty (support sp)
>   nes   = mapPreservesNonEmpty fst (toList sp) (nonEmptyLemma1 sp)
>   nens  : List.Operations.NonEmpty (nub (support sp))
>   nens  = nubPreservesNonEmpty (support sp) nes
>   neaps : List.Operations.NonEmpty aps
>   neaps = mapPreservesNonEmpty (pair (id, (prob sp))) (nub (support sp)) nens 

> |||
> mostProbable : {A : Type} -> (Eq A) => SimpleProb A -> A
> mostProbable = fst . mostProbableProb

> |||
> maxProbability : {A : Type} -> (Eq A) => SimpleProb A -> NonNegDouble
> maxProbability = snd . mostProbableProb

> |||
> sortToList : {A : Type} -> (Eq A) => SimpleProb A -> List (A, NonNegDouble)
> sortToList {A} sp = sortBy ord aps where
>   aps : List (A, NonNegDouble)
>   aps = map (pair (id, (prob sp))) (nub (support sp))
>   ord : (A, NonNegDouble) -> (A, NonNegDouble) -> Ordering
>   ord (a1, pa1) (a2, pa2) = compare (toDouble pa1) (toDouble pa2)

> |||
> naiveMostProbableProb : {A : Type} -> SimpleProb A -> (A, NonNegDouble)
> naiveMostProbableProb sp = argmaxMax totalPreorderLTE (toList sp) (nonEmptyLemma1 sp)

> |||
> naiveMostProbable : {A : Type} -> SimpleProb A -> A
> naiveMostProbable = fst . naiveMostProbableProb

> |||
> naiveMaxProbability : {A : Type} -> SimpleProb A -> NonNegDouble
> naiveMaxProbability = snd . naiveMostProbableProb

> |||
> naiveSortToList : {A : Type} -> SimpleProb A -> List (A, NonNegDouble)
> naiveSortToList {A} sp = sortBy ord (toList sp) where
>   ord : (A, NonNegDouble) -> (A, NonNegDouble) -> Ordering
>   ord (a1, pa1) (a2, pa2) = if (toDouble pa1) == (toDouble pa2)
>                             then EQ
>                             else if (toDouble pa1) < (toDouble pa2)
>                                  then GT
>                                  else LT


> {-

> ---}    




