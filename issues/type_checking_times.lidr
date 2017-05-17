> module IdrisLibs.issues.Main

> import Data.Fin
> import Data.So

> import SequentialDecisionProblems.CoreTheory
> -- import SequentialDecisionProblems.Utils
> import SequentialDecisionProblems.FastStochasticDefaults

> import FastSimpleProb.SimpleProb
> import FastSimpleProb.BasicOperations
> import Double.Predicates
> import Double.Postulates
> import Double.Operations
> import NonNegDouble.NonNegDouble
> import NonNegDouble.Constants
> import NonNegDouble.BasicOperations
> import NonNegDouble.Operations
> import NonNegDouble.Properties
> import NonNegDouble.Predicates
> import Fin.Operations
> import List.Operations

> %auto_implicits off

> SequentialDecisionProblems.CoreTheory.State t 
> = (Fin (S t), Bool, Bool, Bool)

> SequentialDecisionProblems.CoreTheory.Ctrl _ _ = Bool

> crE : Double
> crE = 0.0
> crN : Nat
> crN = 8
> pS1 : NonNegDouble
> pS1 = cast 0.9
> pS2 : NonNegDouble
> pS2 = cast 0.1
> pA1 : NonNegDouble
> pA1 = cast 0.1
> pA2 : NonNegDouble
> pA2 = cast 0.9
> pLH : NonNegDouble
> pLH = cast 0.7

> SequentialDecisionProblems.CoreTheory.nexts t (e, True, False, True) False =
>   let ttres = mkSimpleProb 
>               [((weaken e, False, False,  True),        pLH  * (one - pA1) *        pS1), 
>                ((    FS e,  True, False,  True), (one - pLH) * (one - pA1) *        pS1),
>                ((weaken e, False,  True,  True),        pLH  *        pA1  *        pS1), 
>                ((    FS e,  True,  True,  True), (one - pLH) *        pA1  *        pS1),
>                ((weaken e, False, False, False),        pLH  * (one - pA1) * (one - pS1)), 
>                ((    FS e,  True, False, False), (one - pLH) * (one - pA1) * (one - pS1)),
>                ((weaken e, False,  True, False),        pLH  *        pA1  * (one - pS1)), 
>                ((    FS e,  True,  True, False), (one - pLH) *        pA1  * (one - pS1))] in
>   let tfres = mkSimpleProb 
>               [((weaken e, False, False,  True),        pLH  * (one - pA1) *        pS2), 
>                ((    FS e,  True, False,  True), (one - pLH) * (one - pA1) *        pS2),
>                ((weaken e, False,  True,  True),        pLH  *        pA1  *        pS2), 
>                ((    FS e,  True,  True,  True), (one - pLH) *        pA1  *        pS2),
>                ((weaken e, False, False, False),        pLH  * (one - pA1) * (one - pS2)), 
>                ((    FS e,  True, False, False), (one - pLH) * (one - pA1) * (one - pS2)),
>                ((weaken e, False,  True, False),        pLH  *        pA1  * (one - pS2)), 
>                ((    FS e,  True,  True, False), (one - pLH) *        pA1  * (one - pS2))] in
>   let ftres = mkSimpleProb 
>               [((weaken e, False, False,  True),        pLH  * (one - pA2) *        pS1), 
>                ((    FS e,  True, False,  True), (one - pLH) * (one - pA2) *        pS1),
>                ((weaken e, False,  True,  True),        pLH  *        pA2  *        pS1), 
>                ((    FS e,  True,  True,  True), (one - pLH) *        pA2  *        pS1),
>                ((weaken e, False, False, False),        pLH  * (one - pA2) * (one - pS1)), 
>                ((    FS e,  True, False, False), (one - pLH) * (one - pA2) * (one - pS1)),
>                ((weaken e, False,  True, False),        pLH  *        pA2  * (one - pS1)), 
>                ((    FS e,  True,  True, False), (one - pLH) *        pA2  * (one - pS1))] in
>   let ffres = mkSimpleProb 
>               [((weaken e, False, False,  True),        pLH  * (one - pA2) *        pS2), 
>                ((    FS e,  True, False,  True), (one - pLH) * (one - pA2) *        pS2),
>                ((weaken e, False,  True,  True),        pLH  *        pA2  *        pS2), 
>                ((    FS e,  True,  True,  True), (one - pLH) *        pA2  *        pS2),
>                ((weaken e, False, False, False),        pLH  * (one - pA2) * (one - pS2)), 
>                ((    FS e,  True, False, False), (one - pLH) * (one - pA2) * (one - pS2)),
>                ((weaken e, False,  True, False),        pLH  *        pA2  * (one - pS2)), 
>                ((    FS e,  True,  True, False), (one - pLH) *        pA2  * (one - pS2))] in
>   case (t <= crN) of
>     True  => case (fromFin e <= crE) of
>                True  => ttres
>                False => tfres
>     False => case (fromFin e <= crE) of
>                True  => ftres
>                False => ffres
