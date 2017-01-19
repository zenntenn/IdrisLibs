> module SimpleProb.BasicProperties

> import Data.List
> import Syntax.PreorderReasoning

> import SimpleProb.SimpleProb
> import SimpleProb.BasicOperations
> import NonNegRational.NonNegRational
> import NonNegRational.BasicOperations
> import NonNegRational.BasicProperties
> import Num.Refinements
> import List.Operations
> import List.Properties
> import Nat.Positive
> import Fraction.Normal

> %default total
> %access public export
> %auto_implicits on


> |||
> toListLemma : {A : Type} -> (sp : SimpleProb A) -> sumMapSnd (toList sp) = 1
> toListLemma (MkSimpleProb _ prf) = prf


> ||| 
> sumProbsLemma : {A : Type} -> (sp : SimpleProb A) -> sum (probs sp) = 1
> sumProbsLemma {A} sp = ( sum (map snd (toList (normalize sp))) )
>                      ={ Refl }=
>                        ( sumMapSnd (toList (normalize sp)) )
>                      ={ toListLemma (normalize sp) }=
>                        ( 1 )
>                      QED


> |||
> lengthSupportProbsLemma : {A : Type} -> (sp : SimpleProb A) ->
>                           length (support sp) = length (probs sp)
> lengthSupportProbsLemma sp = lengthLemma (toList (normalize sp)) fst snd                           


> ||| SimpleProb is an implementation of Show
> implementation Show a => Show (SimpleProb a) where
>   show sp = show (toList sp)


> {-

> ---}
