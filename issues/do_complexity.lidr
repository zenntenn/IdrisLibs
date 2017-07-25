> module issues.Main

> import Data.Fin
> import Data.List
> import Data.List.Quantifiers
> import Data.So
> import Effects
> import Effect.Exception
> import Effect.StdIO

> import SequentialDecisionProblems.CoreTheory
> import SequentialDecisionProblems.FullTheory
> import SequentialDecisionProblems.TabBackwardsInduction
> import SequentialDecisionProblems.Utils
> import SequentialDecisionProblems.FastStochasticDefaults
> import SequentialDecisionProblems.CoreTheoryOptDefaults
> import SequentialDecisionProblems.FullTheoryOptDefaults
> import SequentialDecisionProblems.TabBackwardsInductionOptDefaults

> import SequentialDecisionProblems.applications.LowHigh
> import SequentialDecisionProblems.applications.AvailableUnavailable
> import SequentialDecisionProblems.applications.GoodBad

> import FastSimpleProb.SimpleProb
> import FastSimpleProb.BasicOperations
> import FastSimpleProb.BasicProperties
> import FastSimpleProb.MonadicOperations
> import FastSimpleProb.MonadicProperties
> import FastSimpleProb.Measures
> import FastSimpleProb.MeasuresProperties
> import FastSimpleProb.Operations
> import Sigma.Sigma
> import Double.Predicates
> import Double.Postulates
> import Double.Operations
> import Double.Properties
> import NonNegDouble.NonNegDouble
> import NonNegDouble.Constants
> import NonNegDouble.BasicOperations
> import NonNegDouble.Operations
> import NonNegDouble.Properties
> import NonNegDouble.Predicates
> import NonNegDouble.LTEProperties
> import Finite.Predicates
> import Finite.Operations
> import Finite.Properties
> import Decidable.Predicates
> import Decidable.Properties
> import LocalEffect.Exception
> import LocalEffect.StdIO
> import Fin.Operations
> import List.Operations
> import Unit.Properties

> -- %default total
> %auto_implicits off
> -- %logging 5


* Controls

> SequentialDecisionProblems.CoreTheory.Ctrl _ _ = LowHigh


* States

> SequentialDecisionProblems.CoreTheory.State t 
> = (Fin (S t), LowHigh, AvailableUnavailable, GoodBad)


* Transition function

> crE : Double
> crE = 0.0

> crN : Nat
> crN = 8

> pS1  :  NonNegDouble
> pS1  =  cast 0.9

> pS2  :  NonNegDouble
> pS2  =  cast 0.1

> pS2LTEpS1 : pS2 `NonNegDouble.Predicates.LTE` pS1
> pS2LTEpS1 = MkLTE Oh

> pA1  :  NonNegDouble
> pA1  =  cast 0.1

> pA2  :  NonNegDouble
> pA2  =  cast 0.9

> pA1LTEpA2 : pA1 `NonNegDouble.Predicates.LTE` pA2
> pA1LTEpA2 = MkLTE Oh

> pLL  :  NonNegDouble
> pLL  =  cast 0.9

> pLH  :  NonNegDouble
> pLH  =  cast 0.7

> pLHLTEpLL : pLH `NonNegDouble.Predicates.LTE` pLL
> pLHLTEpLL = MkLTE Oh

> pHL  :  NonNegDouble
> pHL  =  cast 0.7

> pHH  :  NonNegDouble
> pHH  =  cast 0.9

> pHLLTEpHH : pHL `NonNegDouble.Predicates.LTE` pHH
> pHLLTEpHH = MkLTE Oh

> SequentialDecisionProblems.CoreTheory.nexts t (e, High, Unavailable, Good) Low =
>   let ttres = mkSimpleProb 
>               [((weaken e, Low,  Unavailable, Good),        pLH  * (one - pA1) *        pS1), 
>                ((    FS e, High, Unavailable, Good), (one - pLH) * (one - pA1) *        pS1),
>                ((weaken e, Low,    Available, Good),        pLH  *        pA1  *        pS1), 
>                ((    FS e, High,   Available, Good), (one - pLH) *        pA1  *        pS1),
>                ((weaken e, Low,  Unavailable,  Bad),        pLH  * (one - pA1) * (one - pS1)), 
>                ((    FS e, High, Unavailable,  Bad), (one - pLH) * (one - pA1) * (one - pS1)),
>                ((weaken e, Low,    Available,  Bad),        pLH  *        pA1  * (one - pS1)), 
>                ((    FS e, High,   Available,  Bad), (one - pLH) *        pA1  * (one - pS1))] in
>   let tfres = mkSimpleProb 
>               [((weaken e, Low,  Unavailable, Good),        pLH  * (one - pA1) *        pS2), 
>                ((    FS e, High, Unavailable, Good), (one - pLH) * (one - pA1) *        pS2),
>                ((weaken e, Low,    Available, Good),        pLH  *        pA1  *        pS2), 
>                ((    FS e, High,   Available, Good), (one - pLH) *        pA1  *        pS2),
>                ((weaken e, Low,  Unavailable,  Bad),        pLH  * (one - pA1) * (one - pS2)), 
>                ((    FS e, High, Unavailable,  Bad), (one - pLH) * (one - pA1) * (one - pS2)),
>                ((weaken e, Low,    Available,  Bad),        pLH  *        pA1  * (one - pS2)), 
>                ((    FS e, High,   Available,  Bad), (one - pLH) *        pA1  * (one - pS2))] in
>   let ftres = mkSimpleProb 
>               [((weaken e, Low,  Unavailable, Good),        pLH  * (one - pA2) *        pS1), 
>                ((    FS e, High, Unavailable, Good), (one - pLH) * (one - pA2) *        pS1),
>                ((weaken e, Low,    Available, Good),        pLH  *        pA2  *        pS1), 
>                ((    FS e, High,   Available, Good), (one - pLH) *        pA2  *        pS1),
>                ((weaken e, Low,  Unavailable,  Bad),        pLH  * (one - pA2) * (one - pS1)), 
>                ((    FS e, High, Unavailable,  Bad), (one - pLH) * (one - pA2) * (one - pS1)),
>                ((weaken e, Low,    Available,  Bad),        pLH  *        pA2  * (one - pS1)), 
>                ((    FS e, High,   Available,  Bad), (one - pLH) *        pA2  * (one - pS1))] in
>   let ffres = mkSimpleProb 
>               [((weaken e, Low,  Unavailable, Good),        pLH  * (one - pA2) *        pS2), 
>                ((    FS e, High, Unavailable, Good), (one - pLH) * (one - pA2) *        pS2),
>                ((weaken e, Low,    Available, Good),        pLH  *        pA2  *        pS2), 
>                ((    FS e, High,   Available, Good), (one - pLH) *        pA2  *        pS2),
>                ((weaken e, Low,  Unavailable,  Bad),        pLH  * (one - pA2) * (one - pS2)), 
>                ((    FS e, High, Unavailable,  Bad), (one - pLH) * (one - pA2) * (one - pS2)),
>                ((weaken e, Low,    Available,  Bad),        pLH  *        pA2  * (one - pS2)), 
>                ((    FS e, High,   Available,  Bad), (one - pLH) *        pA2  * (one - pS2))] in
>   case (t <= crN) of
>     True  => case (fromFin e <= crE) of
>                True  => ttres
>                False => tfres
>     False => case (fromFin e <= crE) of
>                True  => ftres
>                False => ffres
> SequentialDecisionProblems.CoreTheory.nexts t (e, High, Unavailable, Good) High =
>   let ttres = mkSimpleProb 
>               [((weaken e, Low,  Unavailable, Good), (one - pHH) * (one - pA1) *        pS1), 
>                ((    FS e, High, Unavailable, Good),        pHH  * (one - pA1) *        pS1),
>                ((weaken e, Low,    Available, Good), (one - pHH) *        pA1  *        pS1), 
>                ((    FS e, High,   Available, Good),        pHH  *        pA1  *        pS1),
>                ((weaken e, Low,  Unavailable,  Bad), (one - pHH) * (one - pA1) * (one - pS1)), 
>                ((    FS e, High, Unavailable,  Bad),        pHH  * (one - pA1) * (one - pS1)),
>                ((weaken e, Low,    Available,  Bad), (one - pHH) *        pA1  * (one - pS1)), 
>                ((    FS e, High,   Available,  Bad),        pHH  *        pA1  * (one - pS1))] in
>   let tfres = mkSimpleProb 
>               [((weaken e, Low,  Unavailable, Good), (one - pHH) * (one - pA1) *        pS2), 
>                ((    FS e, High, Unavailable, Good),        pHH  * (one - pA1) *        pS2),
>                ((weaken e, Low,    Available, Good), (one - pHH) *        pA1  *        pS2), 
>                ((    FS e, High,   Available, Good),        pHH  *        pA1  *        pS2),
>                ((weaken e, Low,  Unavailable,  Bad), (one - pHH) * (one - pA1) * (one - pS2)), 
>                ((    FS e, High, Unavailable,  Bad),        pHH  * (one - pA1) * (one - pS2)),
>                ((weaken e, Low,    Available,  Bad), (one - pHH) *        pA1  * (one - pS2)), 
>                ((    FS e, High,   Available,  Bad),        pHH  *        pA1  * (one - pS2))] in
>   let ftres = mkSimpleProb 
>               [((weaken e, Low,  Unavailable, Good), (one - pHH) * (one - pA2) *        pS1), 
>                ((    FS e, High, Unavailable, Good),        pHH  * (one - pA2) *        pS1),
>                ((weaken e, Low,    Available, Good), (one - pHH) *        pA2  *        pS1), 
>                ((    FS e, High,   Available, Good),        pHH  *        pA2  *        pS1),
>                ((weaken e, Low,  Unavailable,  Bad), (one - pHH) * (one - pA2) * (one - pS1)), 
>                ((    FS e, High, Unavailable,  Bad),        pHH  * (one - pA2) * (one - pS1)),
>                ((weaken e, Low,    Available,  Bad), (one - pHH) *        pA2  * (one - pS1)), 
>                ((    FS e, High,   Available,  Bad),        pHH  *        pA2  * (one - pS1))] in
>   let ffres = mkSimpleProb 
>               [((weaken e, Low,  Unavailable, Good), (one - pHH) * (one - pA2) *        pS2), 
>                ((    FS e, High, Unavailable, Good),        pHH  * (one - pA2) *        pS2),
>                ((weaken e, Low,    Available, Good), (one - pHH) *        pA2  *        pS2), 
>                ((    FS e, High,   Available, Good),        pHH  *        pA2  *        pS2),
>                ((weaken e, Low,  Unavailable,  Bad), (one - pHH) * (one - pA2) * (one - pS2)), 
>                ((    FS e, High, Unavailable,  Bad),        pHH  * (one - pA2) * (one - pS2)),
>                ((weaken e, Low,    Available,  Bad), (one - pHH) *        pA2  * (one - pS2)), 
>                ((    FS e, High,   Available,  Bad),        pHH  *        pA2  * (one - pS2))] in
>   case (t <= crN) of
>     True  => case (fromFin e <= crE) of
>                True  => ttres
>                False => tfres
>     False => case (fromFin e <= crE) of
>                True  => ftres
>                False => ffres
>
> SequentialDecisionProblems.CoreTheory.nexts t (e, High, Unavailable, Bad) Low =
>   let ttres = mkSimpleProb 
>               [((weaken e, Low,  Unavailable,  Bad),        pLH  * (one - pA1)), 
>                ((    FS e, High, Unavailable,  Bad), (one - pLH) * (one - pA1)),
>                ((weaken e, Low,    Available,  Bad),        pLH  *        pA1 ), 
>                ((    FS e, High,   Available,  Bad), (one - pLH) *        pA1 )] in
>   let tfres = mkSimpleProb 
>               [((weaken e, Low,  Unavailable,  Bad),        pLH  * (one - pA1)), 
>                ((    FS e, High, Unavailable,  Bad), (one - pLH) * (one - pA1)),
>                ((weaken e, Low,    Available,  Bad),        pLH  *        pA1 ), 
>                ((    FS e, High,   Available,  Bad), (one - pLH) *        pA1 )] in
>   let ftres = mkSimpleProb 
>               [((weaken e, Low,  Unavailable,  Bad),        pLH  * (one - pA2)), 
>                ((    FS e, High, Unavailable,  Bad), (one - pLH) * (one - pA2)),
>                ((weaken e, Low,    Available,  Bad),        pLH  *        pA2 ), 
>                ((    FS e, High,   Available,  Bad), (one - pLH) *        pA2 )] in
>   let ffres = mkSimpleProb 
>               [((weaken e, Low,  Unavailable,  Bad),        pLH  * (one - pA2)), 
>                ((    FS e, High, Unavailable,  Bad), (one - pLH) * (one - pA2)),
>                ((weaken e, Low,    Available,  Bad),        pLH  *        pA2 ), 
>                ((    FS e, High,   Available,  Bad), (one - pLH) *        pA2 )] in
>   case (t <= crN) of
>     True  => case (fromFin e <= crE) of
>                True  => ttres
>                False => tfres
>     False => case (fromFin e <= crE) of
>                True  => ftres
>                False => ffres
> SequentialDecisionProblems.CoreTheory.nexts t (e, High, Unavailable, Bad) High =
>   let ttres = mkSimpleProb 
>               [((weaken e, Low,  Unavailable,  Bad), (one - pHH) * (one - pA1)), 
>                ((    FS e, High, Unavailable,  Bad),        pHH  * (one - pA1)),
>                ((weaken e, Low,    Available,  Bad), (one - pHH) *        pA1 ), 
>                ((    FS e, High,   Available,  Bad),        pHH  *        pA1 )] in
>   let tfres = mkSimpleProb 
>               [((weaken e, Low,  Unavailable,  Bad), (one - pHH) * (one - pA1)), 
>                ((    FS e, High, Unavailable,  Bad),        pHH  * (one - pA1)),
>                ((weaken e, Low,    Available,  Bad), (one - pHH) *        pA1 ), 
>                ((    FS e, High,   Available,  Bad),        pHH  *        pA1 )] in
>   let ftres = mkSimpleProb 
>               [((weaken e, Low,  Unavailable,  Bad), (one - pHH) * (one - pA2)), 
>                ((    FS e, High, Unavailable,  Bad),        pHH  * (one - pA2)),
>                ((weaken e, Low,    Available,  Bad), (one - pHH) *        pA2 ), 
>                ((    FS e, High,   Available,  Bad),        pHH  *        pA2 )] in
>   let ffres = mkSimpleProb 
>               [((weaken e, Low,  Unavailable,  Bad), (one - pHH) * (one - pA2)), 
>                ((    FS e, High, Unavailable,  Bad),        pHH  * (one - pA2)),
>                ((weaken e, Low,    Available,  Bad), (one - pHH) *        pA2 ), 
>                ((    FS e, High,   Available,  Bad),        pHH  *        pA2 )] in
>   case (t <= crN) of
>     True  => case (fromFin e <= crE) of
>                True  => ttres
>                False => tfres
>     False => case (fromFin e <= crE) of
>                True  => ftres
>                False => ffres
>
>
> SequentialDecisionProblems.CoreTheory.nexts t (e, High, Available, Good) Low =
>   let ttres = mkSimpleProb 
>               [((weaken e, Low,    Available, Good),        pLH  *        pS1), 
>                ((    FS e, High,   Available, Good), (one - pLH) *        pS1),
>                ((weaken e, Low,    Available,  Bad),        pLH  * (one - pS1)), 
>                ((    FS e, High,   Available,  Bad), (one - pLH) * (one - pS1))] in
>   let tfres = mkSimpleProb 
>               [((weaken e, Low,    Available, Good),        pLH  *        pS2), 
>                ((    FS e, High,   Available, Good), (one - pLH) *        pS2),
>                ((weaken e, Low,    Available,  Bad),        pLH  * (one - pS2)), 
>                ((    FS e, High,   Available,  Bad), (one - pLH) * (one - pS2))] in
>   let ftres = mkSimpleProb 
>               [((weaken e, Low,    Available, Good),        pLH  *        pS1), 
>                ((    FS e, High,   Available, Good), (one - pLH) *        pS1),
>                ((weaken e, Low,    Available,  Bad),        pLH  * (one - pS1)), 
>                ((    FS e, High,   Available,  Bad), (one - pLH) * (one - pS1))] in
>   let ffres = mkSimpleProb 
>               [((weaken e, Low,    Available, Good),        pLH  *        pS2), 
>                ((    FS e, High,   Available, Good), (one - pLH) *        pS2),
>                ((weaken e, Low,    Available,  Bad),        pLH  * (one - pS2)), 
>                ((    FS e, High,   Available,  Bad), (one - pLH) * (one - pS2))] in
>   case (t <= crN) of
>     True  => case (fromFin e <= crE) of
>                True  => ttres
>                False => tfres
>     False => case (fromFin e <= crE) of
>                True  => ftres
>                False => ffres
> SequentialDecisionProblems.CoreTheory.nexts t (e, High, Available, Good) High =
>   let ttres = mkSimpleProb 
>               [((weaken e, Low,    Available, Good), (one - pHH) *        pS1), 
>                ((    FS e, High,   Available, Good),        pHH  *        pS1),
>                ((weaken e, Low,    Available,  Bad), (one - pHH) * (one - pS1)), 
>                ((    FS e, High,   Available,  Bad),        pHH  * (one - pS1))] in
>   let tfres = mkSimpleProb 
>               [((weaken e, Low,    Available, Good), (one - pHH) *        pS2), 
>                ((    FS e, High,   Available, Good),        pHH  *        pS2),
>                ((weaken e, Low,    Available,  Bad), (one - pHH) * (one - pS2)), 
>                ((    FS e, High,   Available,  Bad),        pHH  * (one - pS2))] in
>   let ftres = mkSimpleProb 
>               [((weaken e, Low,    Available, Good), (one - pHH) *        pS1), 
>                ((    FS e, High,   Available, Good),        pHH  *        pS1),
>                ((weaken e, Low,    Available,  Bad), (one - pHH) * (one - pS1)), 
>                ((    FS e, High,   Available,  Bad),        pHH  * (one - pS1))] in
>   let ffres = mkSimpleProb 
>               [((weaken e, Low,    Available, Good), (one - pHH) *        pS2), 
>                ((    FS e, High,   Available, Good),        pHH  *        pS2),
>                ((weaken e, Low,    Available,  Bad), (one - pHH) * (one - pS2)), 
>                ((    FS e, High,   Available,  Bad),        pHH  * (one - pS2))] in
>   case (t <= crN) of
>     True  => case (fromFin e <= crE) of
>                True  => ttres
>                False => tfres
>     False => case (fromFin e <= crE) of
>                True  => ftres
>                False => ffres
>
> SequentialDecisionProblems.CoreTheory.nexts t (e, High, Available, Bad) Low =
>   let ttres = mkSimpleProb 
>               [((weaken e, Low,    Available,  Bad),        pLH ), 
>                ((    FS e, High,   Available,  Bad), (one - pLH))] in
>   let tfres = mkSimpleProb 
>               [((weaken e, Low,    Available,  Bad),        pLH ), 
>                ((    FS e, High,   Available,  Bad), (one - pLH))] in
>   let ftres = mkSimpleProb 
>               [((weaken e, Low,    Available,  Bad),        pLH ), 
>                ((    FS e, High,   Available,  Bad), (one - pLH))] in
>   let ffres = mkSimpleProb 
>               [((weaken e, Low,    Available,  Bad),        pLH ), 
>                ((    FS e, High,   Available,  Bad), (one - pLH))] in
>   case (t <= crN) of
>     True  => case (fromFin e <= crE) of
>                True  => ttres
>                False => tfres
>     False => case (fromFin e <= crE) of
>                True  => ftres
>                False => ffres
> SequentialDecisionProblems.CoreTheory.nexts t (e, High, Available, Bad) High =
>   let ttres = mkSimpleProb 
>               [((weaken e, Low,    Available,  Bad), (one - pHH)), 
>                ((    FS e, High,   Available,  Bad),        pHH )] in
>   let tfres = mkSimpleProb 
>               [((weaken e, Low,    Available,  Bad), (one - pHH)), 
>                ((    FS e, High,   Available,  Bad),        pHH )] in
>   let ftres = mkSimpleProb 
>               [((weaken e, Low,    Available,  Bad), (one - pHH)), 
>                ((    FS e, High,   Available,  Bad),        pHH )] in
>   let ffres = mkSimpleProb 
>               [((weaken e, Low,    Available,  Bad), (one - pHH)), 
>                ((    FS e, High,   Available,  Bad),        pHH )] in
>   case (t <= crN) of
>     True  => case (fromFin e <= crE) of
>                True  => ttres
>                False => tfres
>     False => case (fromFin e <= crE) of
>                True  => ftres
>                False => ffres
>
>
>
>
> SequentialDecisionProblems.CoreTheory.nexts t (e, Low, Unavailable, Good) Low =
>   let ttres = mkSimpleProb 
>               [((weaken e, Low,  Unavailable, Good),        pLL  * (one - pA1) *        pS1), 
>                ((    FS e, High, Unavailable, Good), (one - pLL) * (one - pA1) *        pS1),
>                ((weaken e, Low,    Available, Good),        pLL  *        pA1  *        pS1), 
>                ((    FS e, High,   Available, Good), (one - pLL) *        pA1  *        pS1),
>                ((weaken e, Low,  Unavailable,  Bad),        pLL  * (one - pA1) * (one - pS1)), 
>                ((    FS e, High, Unavailable,  Bad), (one - pLL) * (one - pA1) * (one - pS1)),
>                ((weaken e, Low,    Available,  Bad),        pLL  *        pA1  * (one - pS1)), 
>                ((    FS e, High,   Available,  Bad), (one - pLL) *        pA1  * (one - pS1))] in
>   let tfres = mkSimpleProb 
>               [((weaken e, Low,  Unavailable, Good),        pLL  * (one - pA1) *        pS2), 
>                ((    FS e, High, Unavailable, Good), (one - pLL) * (one - pA1) *        pS2),
>                ((weaken e, Low,    Available, Good),        pLL  *        pA1  *        pS2), 
>                ((    FS e, High,   Available, Good), (one - pLL) *        pA1  *        pS2),
>                ((weaken e, Low,  Unavailable,  Bad),        pLL  * (one - pA1) * (one - pS2)), 
>                ((    FS e, High, Unavailable,  Bad), (one - pLL) * (one - pA1) * (one - pS2)),
>                ((weaken e, Low,    Available,  Bad),        pLL  *        pA1  * (one - pS2)), 
>                ((    FS e, High,   Available,  Bad), (one - pLL) *        pA1  * (one - pS2))] in
>   let ftres = mkSimpleProb 
>               [((weaken e, Low,  Unavailable, Good),        pLL  * (one - pA2) *        pS1), 
>                ((    FS e, High, Unavailable, Good), (one - pLL) * (one - pA2) *        pS1),
>                ((weaken e, Low,    Available, Good),        pLL  *        pA2  *        pS1), 
>                ((    FS e, High,   Available, Good), (one - pLL) *        pA2  *        pS1),
>                ((weaken e, Low,  Unavailable,  Bad),        pLL  * (one - pA2) * (one - pS1)), 
>                ((    FS e, High, Unavailable,  Bad), (one - pLL) * (one - pA2) * (one - pS1)),
>                ((weaken e, Low,    Available,  Bad),        pLL  *        pA2  * (one - pS1)), 
>                ((    FS e, High,   Available,  Bad), (one - pLL) *        pA2  * (one - pS1))] in
>   let ffres = mkSimpleProb 
>               [((weaken e, Low,  Unavailable, Good),        pLL  * (one - pA2) *        pS2), 
>                ((    FS e, High, Unavailable, Good), (one - pLL) * (one - pA2) *        pS2),
>                ((weaken e, Low,    Available, Good),        pLL  *        pA2  *        pS2), 
>                ((    FS e, High,   Available, Good), (one - pLL) *        pA2  *        pS2),
>                ((weaken e, Low,  Unavailable,  Bad),        pLL  * (one - pA2) * (one - pS2)), 
>                ((    FS e, High, Unavailable,  Bad), (one - pLL) * (one - pA2) * (one - pS2)),
>                ((weaken e, Low,    Available,  Bad),        pLL  *        pA2  * (one - pS2)), 
>                ((    FS e, High,   Available,  Bad), (one - pLL) *        pA2  * (one - pS2))] in
>   case (t <= crN) of
>     True  => case (fromFin e <= crE) of
>                True  => ttres
>                False => tfres
>     False => case (fromFin e <= crE) of
>                True  => ftres
>                False => ffres
> SequentialDecisionProblems.CoreTheory.nexts t (e, Low, Unavailable, Good) High =
>   let ttres = mkSimpleProb 
>               [((weaken e, Low,  Unavailable, Good), (one - pHL) * (one - pA1) *        pS1), 
>                ((    FS e, High, Unavailable, Good),        pHL  * (one - pA1) *        pS1),
>                ((weaken e, Low,    Available, Good), (one - pHL) *        pA1  *        pS1), 
>                ((    FS e, High,   Available, Good),        pHL  *        pA1  *        pS1),
>                ((weaken e, Low,  Unavailable,  Bad), (one - pHL) * (one - pA1) * (one - pS1)), 
>                ((    FS e, High, Unavailable,  Bad),        pHL  * (one - pA1) * (one - pS1)),
>                ((weaken e, Low,    Available,  Bad), (one - pHL) *        pA1  * (one - pS1)), 
>                ((    FS e, High,   Available,  Bad),        pHL  *        pA1  * (one - pS1))] in
>   let tfres = mkSimpleProb 
>               [((weaken e, Low,  Unavailable, Good), (one - pHL) * (one - pA1) *        pS2), 
>                ((    FS e, High, Unavailable, Good),        pHL  * (one - pA1) *        pS2),
>                ((weaken e, Low,    Available, Good), (one - pHL) *        pA1  *        pS2), 
>                ((    FS e, High,   Available, Good),        pHL  *        pA1  *        pS2),
>                ((weaken e, Low,  Unavailable,  Bad), (one - pHL) * (one - pA1) * (one - pS2)), 
>                ((    FS e, High, Unavailable,  Bad),        pHL  * (one - pA1) * (one - pS2)),
>                ((weaken e, Low,    Available,  Bad), (one - pHL) *        pA1  * (one - pS2)), 
>                ((    FS e, High,   Available,  Bad),        pHL  *        pA1  * (one - pS2))] in
>   let ftres = mkSimpleProb 
>               [((weaken e, Low,  Unavailable, Good), (one - pHL) * (one - pA2) *        pS1), 
>                ((    FS e, High, Unavailable, Good),        pHL  * (one - pA2) *        pS1),
>                ((weaken e, Low,    Available, Good), (one - pHL) *        pA2  *        pS1), 
>                ((    FS e, High,   Available, Good),        pHL  *        pA2  *        pS1),
>                ((weaken e, Low,  Unavailable,  Bad), (one - pHL) * (one - pA2) * (one - pS1)), 
>                ((    FS e, High, Unavailable,  Bad),        pHL  * (one - pA2) * (one - pS1)),
>                ((weaken e, Low,    Available,  Bad), (one - pHL) *        pA2  * (one - pS1)), 
>                ((    FS e, High,   Available,  Bad),        pHL  *        pA2  * (one - pS1))] in
>   let ffres = mkSimpleProb 
>               [((weaken e, Low,  Unavailable, Good), (one - pHL) * (one - pA2) *        pS2), 
>                ((    FS e, High, Unavailable, Good),        pHL  * (one - pA2) *        pS2),
>                ((weaken e, Low,    Available, Good), (one - pHL) *        pA2  *        pS2), 
>                ((    FS e, High,   Available, Good),        pHL  *        pA2  *        pS2),
>                ((weaken e, Low,  Unavailable,  Bad), (one - pHL) * (one - pA2) * (one - pS2)), 
>                ((    FS e, High, Unavailable,  Bad),        pHL  * (one - pA2) * (one - pS2)),
>                ((weaken e, Low,    Available,  Bad), (one - pHL) *        pA2  * (one - pS2)), 
>                ((    FS e, High,   Available,  Bad),        pHL  *        pA2  * (one - pS2))] in
>   case (t <= crN) of
>     True  => case (fromFin e <= crE) of
>                True  => ttres
>                False => tfres
>     False => case (fromFin e <= crE) of
>                True  => ftres
>                False => ffres
>
> SequentialDecisionProblems.CoreTheory.nexts t (e, Low, Unavailable, Bad) Low =
>   let ttres = mkSimpleProb 
>               [((weaken e, Low,  Unavailable,  Bad),        pLL  * (one - pA1)), 
>                ((    FS e, High, Unavailable,  Bad), (one - pLL) * (one - pA1)),
>                ((weaken e, Low,    Available,  Bad),        pLL  *        pA1 ), 
>                ((    FS e, High,   Available,  Bad), (one - pLL) *        pA1 )] in
>   let tfres = mkSimpleProb 
>               [((weaken e, Low,  Unavailable,  Bad),        pLL  * (one - pA1)), 
>                ((    FS e, High, Unavailable,  Bad), (one - pLL) * (one - pA1)),
>                ((weaken e, Low,    Available,  Bad),        pLL  *        pA1 ), 
>                ((    FS e, High,   Available,  Bad), (one - pLL) *        pA1 )] in
>   let ftres = mkSimpleProb 
>               [((weaken e, Low,  Unavailable,  Bad),        pLL  * (one - pA2)), 
>                ((    FS e, High, Unavailable,  Bad), (one - pLL) * (one - pA2)),
>                ((weaken e, Low,    Available,  Bad),        pLL  *        pA2 ), 
>                ((    FS e, High,   Available,  Bad), (one - pLL) *        pA2 )] in
>   let ffres = mkSimpleProb 
>               [((weaken e, Low,  Unavailable,  Bad),        pLL  * (one - pA2)), 
>                ((    FS e, High, Unavailable,  Bad), (one - pLL) * (one - pA2)),
>                ((weaken e, Low,    Available,  Bad),        pLL  *        pA2 ), 
>                ((    FS e, High,   Available,  Bad), (one - pLL) *        pA2 )] in
>   case (t <= crN) of
>     True  => case (fromFin e <= crE) of
>                True  => ttres
>                False => tfres
>     False => case (fromFin e <= crE) of
>                True  => ftres
>                False => ffres
> SequentialDecisionProblems.CoreTheory.nexts t (e, Low, Unavailable, Bad) High =
>   let ttres = mkSimpleProb 
>               [((weaken e, Low,  Unavailable,  Bad), (one - pHL) * (one - pA1)), 
>                ((    FS e, High, Unavailable,  Bad),        pHL  * (one - pA1)),
>                ((weaken e, Low,    Available,  Bad), (one - pHL) *        pA1 ), 
>                ((    FS e, High,   Available,  Bad),        pHL  *        pA1 )] in
>   let tfres = mkSimpleProb 
>               [((weaken e, Low,  Unavailable,  Bad), (one - pHL) * (one - pA1)), 
>                ((    FS e, High, Unavailable,  Bad),        pHL  * (one - pA1)),
>                ((weaken e, Low,    Available,  Bad), (one - pHL) *        pA1 ), 
>                ((    FS e, High,   Available,  Bad),        pHL  *        pA1 )] in
>   let ftres = mkSimpleProb 
>               [((weaken e, Low,  Unavailable,  Bad), (one - pHL) * (one - pA2)), 
>                ((    FS e, High, Unavailable,  Bad),        pHL  * (one - pA2)),
>                ((weaken e, Low,    Available,  Bad), (one - pHL) *        pA2 ), 
>                ((    FS e, High,   Available,  Bad),        pHL  *        pA2 )] in
>   let ffres = mkSimpleProb 
>               [((weaken e, Low,  Unavailable,  Bad), (one - pHL) * (one - pA2)), 
>                ((    FS e, High, Unavailable,  Bad),        pHL  * (one - pA2)),
>                ((weaken e, Low,    Available,  Bad), (one - pHL) *        pA2 ), 
>                ((    FS e, High,   Available,  Bad),        pHL  *        pA2 )] in
>   case (t <= crN) of
>     True  => case (fromFin e <= crE) of
>                True  => ttres
>                False => tfres
>     False => case (fromFin e <= crE) of
>                True  => ftres
>                False => ffres
>
>
> SequentialDecisionProblems.CoreTheory.nexts t (e, Low, Available, Good) Low =
>   let ttres = mkSimpleProb 
>               [((weaken e, Low,    Available, Good),        pLL  *        pS1), 
>                ((    FS e, High,   Available, Good), (one - pLL) *        pS1),
>                ((weaken e, Low,    Available,  Bad),        pLL  * (one - pS1)), 
>                ((    FS e, High,   Available,  Bad), (one - pLL) * (one - pS1))] in
>   let tfres = mkSimpleProb 
>               [((weaken e, Low,    Available, Good),        pLL  *        pS2), 
>                ((    FS e, High,   Available, Good), (one - pLL) *        pS2),
>                ((weaken e, Low,    Available,  Bad),        pLL  * (one - pS2)), 
>                ((    FS e, High,   Available,  Bad), (one - pLL) * (one - pS2))] in
>   let ftres = mkSimpleProb 
>               [((weaken e, Low,    Available, Good),        pLL  *        pS1), 
>                ((    FS e, High,   Available, Good), (one - pLL) *        pS1),
>                ((weaken e, Low,    Available,  Bad),        pLL  * (one - pS1)), 
>                ((    FS e, High,   Available,  Bad), (one - pLL) * (one - pS1))] in
>   let ffres = mkSimpleProb 
>               [((weaken e, Low,    Available, Good),        pLL  *        pS2), 
>                ((    FS e, High,   Available, Good), (one - pLL) *        pS2),
>                ((weaken e, Low,    Available,  Bad),        pLL  * (one - pS2)), 
>                ((    FS e, High,   Available,  Bad), (one - pLL) * (one - pS2))] in
>   case (t <= crN) of
>     True  => case (fromFin e <= crE) of
>                True  => ttres
>                False => tfres
>     False => case (fromFin e <= crE) of
>                True  => ftres
>                False => ffres
> SequentialDecisionProblems.CoreTheory.nexts t (e, Low, Available, Good) High =
>   let ttres = mkSimpleProb 
>               [((weaken e, Low,    Available, Good), (one - pHL) *        pS1), 
>                ((    FS e, High,   Available, Good),        pHL  *        pS1),
>                ((weaken e, Low,    Available,  Bad), (one - pHL) * (one - pS1)), 
>                ((    FS e, High,   Available,  Bad),        pHL  * (one - pS1))] in
>   let tfres = mkSimpleProb 
>               [((weaken e, Low,    Available, Good), (one - pHL) *        pS2), 
>                ((    FS e, High,   Available, Good),        pHL  *        pS2),
>                ((weaken e, Low,    Available,  Bad), (one - pHL) * (one - pS2)), 
>                ((    FS e, High,   Available,  Bad),        pHL  * (one - pS2))] in
>   let ftres = mkSimpleProb 
>               [((weaken e, Low,    Available, Good), (one - pHL) *        pS1), 
>                ((    FS e, High,   Available, Good),        pHL  *        pS1),
>                ((weaken e, Low,    Available,  Bad), (one - pHL) * (one - pS1)), 
>                ((    FS e, High,   Available,  Bad),        pHL  * (one - pS1))] in
>   let ffres = mkSimpleProb 
>               [((weaken e, Low,    Available, Good), (one - pHL) *        pS2), 
>                ((    FS e, High,   Available, Good),        pHL  *        pS2),
>                ((weaken e, Low,    Available,  Bad), (one - pHL) * (one - pS2)), 
>                ((    FS e, High,   Available,  Bad),        pHL  * (one - pS2))] in
>   case (t <= crN) of
>     True  => case (fromFin e <= crE) of
>                True  => ttres
>                False => tfres
>     False => case (fromFin e <= crE) of
>                True  => ftres
>                False => ffres
>
> SequentialDecisionProblems.CoreTheory.nexts t (e, Low, Available, Bad) Low =
>   let ttres = mkSimpleProb 
>               [((weaken e, Low,    Available,  Bad),        pLL ), 
>                ((    FS e, High,   Available,  Bad), (one - pLL))] in
>   let tfres = mkSimpleProb 
>               [((weaken e, Low,    Available,  Bad),        pLL ), 
>                ((    FS e, High,   Available,  Bad), (one - pLL))] in
>   let ftres = mkSimpleProb 
>               [((weaken e, Low,    Available,  Bad),        pLL ), 
>                ((    FS e, High,   Available,  Bad), (one - pLL))] in
>   let ffres = mkSimpleProb 
>               [((weaken e, Low,    Available,  Bad),        pLL ), 
>                ((    FS e, High,   Available,  Bad), (one - pLL))] in
>   case (t <= crN) of
>     True  => case (fromFin e <= crE) of
>                True  => ttres
>                False => tfres
>     False => case (fromFin e <= crE) of
>                True  => ftres
>                False => ffres
> SequentialDecisionProblems.CoreTheory.nexts t (e, Low, Available, Bad) High =
>   let ttres = mkSimpleProb 
>               [((weaken e, Low,    Available,  Bad), (one - pHL)), 
>                ((    FS e, High,   Available,  Bad),        pHL )] in
>   let tfres = mkSimpleProb 
>               [((weaken e, Low,    Available,  Bad), (one - pHL)), 
>                ((    FS e, High,   Available,  Bad),        pHL )] in
>   let ftres = mkSimpleProb 
>               [((weaken e, Low,    Available,  Bad), (one - pHL)), 
>                ((    FS e, High,   Available,  Bad),        pHL )] in
>   let ffres = mkSimpleProb 
>               [((weaken e, Low,    Available,  Bad), (one - pHL)), 
>                ((    FS e, High,   Available,  Bad),        pHL )] in
>   case (t <= crN) of
>     True  => case (fromFin e <= crE) of
>                True  => ttres
>                False => tfres
>     False => case (fromFin e <= crE) of
>                True  => ftres
>                False => ffres


* |Val| and |LTE|:

> SequentialDecisionProblems.CoreTheory.Val =
>   NonNegDouble.NonNegDouble
 
> SequentialDecisionProblems.CoreTheory.plus =
>   NonNegDouble.Operations.plus

> SequentialDecisionProblems.CoreTheory.zero =
>   fromInteger 0

> SequentialDecisionProblems.CoreTheory.LTE =
>   NonNegDouble.Predicates.LTE

> SequentialDecisionProblems.FullTheory.reflexiveLTE =
>   NonNegDouble.LTEProperties.reflexiveLTE

> SequentialDecisionProblems.FullTheory.transitiveLTE =
>   NonNegDouble.LTEProperties.transitiveLTE
 
> SequentialDecisionProblems.FullTheory.monotonePlusLTE =
>   NonNegDouble.LTEProperties.monotonePlusLTE

> SequentialDecisionProblems.CoreTheoryOptDefaults.totalPreorderLTE =
>   NonNegDouble.LTEProperties.totalPreorderLTE


* Reward function

> badOverGood : NonNegDouble
> badOverGood = cast 0.5

> badOverGoodLTEone : badOverGood `NonNegDouble.Predicates.LTE` one
> badOverGoodLTEone = MkLTE Oh

> lowOverGoodUnavailable : NonNegDouble
> lowOverGoodUnavailable = cast 0.1

> lowOverGoodAvailable : NonNegDouble
> lowOverGoodAvailable = cast 0.2

> highOverGood : NonNegDouble
> highOverGood = cast 0.3

> lowOverGoodUnavailableLTEone : lowOverGoodUnavailable `NonNegDouble.Predicates.LTE` one
> lowOverGoodUnavailableLTEone = MkLTE Oh

> lowOverGoodAvailableLTEone : lowOverGoodAvailable `NonNegDouble.Predicates.LTE` one
> lowOverGoodAvailableLTEone = MkLTE Oh

> lowOverGoodUnavailableLTElowOverGoodAvailable : lowOverGoodUnavailable `NonNegDouble.Predicates.LTE` lowOverGoodAvailable
> lowOverGoodUnavailableLTElowOverGoodAvailable = MkLTE Oh

> highOverGoodLTEone : highOverGood `NonNegDouble.Predicates.LTE` one
> highOverGoodLTEone = MkLTE Oh

> lowLTEhigh : lowOverGoodAvailable `NonNegDouble.Predicates.LTE` highOverGood
> lowLTEhigh = MkLTE Oh

> SequentialDecisionProblems.CoreTheory.reward _ _ _ (e, High, Unavailable, Good) =
>   one               + one * highOverGood
> SequentialDecisionProblems.CoreTheory.reward _ _ _ (e, High, Unavailable,  Bad) =
>   one * badOverGood + one * highOverGood
>
> SequentialDecisionProblems.CoreTheory.reward _ _ _ (e, High,   Available, Good) =
>   one               + one * highOverGood
> SequentialDecisionProblems.CoreTheory.reward _ _ _ (e, High,   Available,  Bad) =
>   one * badOverGood + one * highOverGood
>   
> SequentialDecisionProblems.CoreTheory.reward _ _ _ (e,  Low, Unavailable, Good) =
>   one               + one * lowOverGoodUnavailable
> SequentialDecisionProblems.CoreTheory.reward _ _ _ (e,  Low, Unavailable,  Bad) =
>   one * badOverGood + one * lowOverGoodUnavailable
>
> SequentialDecisionProblems.CoreTheory.reward _ _ _ (e,  Low,   Available, Good) =
>   one               + one * lowOverGoodAvailable
> SequentialDecisionProblems.CoreTheory.reward _ _ _ (e,  Low,   Available,  Bad) =
>   one * badOverGood + one * lowOverGoodAvailable

 
* Completing the problem specification

> SequentialDecisionProblems.CoreTheory.meas = expectedValue
> SequentialDecisionProblems.FullTheory.measMon = monotoneExpectedValue

> SequentialDecisionProblems.CoreTheory.Viable n x = Unit

> viableLemma : {t, n : Nat} -> (xs : List (State t)) -> All (Viable n) xs
> viableLemma  Nil      = Nil
> viableLemma {t} {n} (x :: xs) = () :: (viableLemma {t} {n} xs)

> SequentialDecisionProblems.CoreTheory.viableSpec1 {t} {n} s v =
>   MkSigma Low (ne, av) where
>     ne : SequentialDecisionProblems.CoreTheory.NotEmpty (nexts t s Low)
>     ne = nonEmptyLemma (nexts t s Low)
>     av : SequentialDecisionProblems.CoreTheory.All (Viable {t = S t} n) (nexts t s Low)
>     av = viableLemma {t = S t} (support (nexts t s Low))

> SequentialDecisionProblems.Utils.finiteViable n x = finiteUnit

> SequentialDecisionProblems.Utils.decidableViable n x = decidableUnit

> SequentialDecisionProblems.CoreTheory.Reachable x' = Unit

> SequentialDecisionProblems.CoreTheory.reachableSpec1 {t} x r y = all (nexts t x y) where
>   all : (sp : SimpleProb  (State (S t))) -> SequentialDecisionProblems.CoreTheory.All (Reachable {t' = S t}) sp
>   all sp = all' (support sp) where
>     all' : (xs : List (State (S t))) -> Data.List.Quantifiers.All (Reachable {t' = S t}) xs
>     all' Nil = Nil
>     all' (x :: xs) = () :: (all' xs)

> SequentialDecisionProblems.TabBackwardsInduction.decidableReachable x = decidableUnit

> SequentialDecisionProblems.Utils.finiteCtrl _ = finiteLowHigh

> SequentialDecisionProblems.TabBackwardsInduction.finiteState t =
>   finiteTuple4 finiteFin finiteLowHigh finiteAvailableUnavailable finiteGoodBad


* Optimal policies, optimal decisions, ...

> SequentialDecisionProblems.Utils.showState {t} (e, High, Unavailable, Good) =
>   "(" ++ show (finToNat e) ++ ",H,U,G)"
> SequentialDecisionProblems.Utils.showState {t} (e, High, Unavailable,  Bad) =
>   "(" ++ show (finToNat e) ++ ",H,U,B)"
> SequentialDecisionProblems.Utils.showState {t} (e, High,   Available, Good) =
>   "(" ++ show (finToNat e) ++ ",H,A,G)"
> SequentialDecisionProblems.Utils.showState {t} (e, High,   Available,  Bad) =
>   "(" ++ show (finToNat e) ++ ",H,A,B)"
> SequentialDecisionProblems.Utils.showState {t} (e,  Low, Unavailable, Good) =
>   "(" ++ show (finToNat e) ++ ",L,U,G)"
> SequentialDecisionProblems.Utils.showState {t} (e,  Low, Unavailable,  Bad) =
>   "(" ++ show (finToNat e) ++ ",L,U,B)"
> SequentialDecisionProblems.Utils.showState {t} (e,  Low,   Available, Good) =
>   "(" ++ show (finToNat e) ++ ",L,A,G)"
> SequentialDecisionProblems.Utils.showState {t} (e,  Low,   Available,  Bad) =
>   "(" ++ show (finToNat e) ++ ",L,A,B)"

> SequentialDecisionProblems.Utils.showCtrl {t} {x}  Low = "L"
> SequentialDecisionProblems.Utils.showCtrl {t} {x} High = "H"

> adHocPossibleStateCtrlSeqs : {t, n : Nat} -> 
>                              (ps : PolicySeq t n) ->
>                              (x : State t) -> 
>                              SimpleProb (StateCtrlSeq t n)
> adHocPossibleStateCtrlSeqs {t} {n = Z}         Nil  x =  
>   FastSimpleProb.MonadicOperations.ret (Nil x)
> adHocPossibleStateCtrlSeqs {t} {n = S m} (p :: ps') x =
>   FastSimpleProb.MonadicOperations.fmap ((MkSigma x y) ::) (FastSimpleProb.MonadicOperations.bind mx' f) where
>     y   :  Ctrl t x
>     y   =  ctrl (p x () ())
>     mx' :  SimpleProb (State (S t))
>     mx' =  nexts t x y
>     f   :  State (S t) -> M (StateCtrlSeq (S t) m)
>     f   =  adHocPossibleStateCtrlSeqs {n = m} ps'

> {-
> computation : { [STDIO] } Eff ()
> computation =
>   do putStr ("enter number of steps:\n")
>      nSteps <- getNat
>      
>      putStrLn "computing optimal policies ..."
>      ps <- pure (tabTailRecursiveBackwardsInduction Z nSteps)
>                      
>      putStrLn "computing possible state-control sequences ..."
>      mxys <- pure (adHocPossibleStateCtrlSeqs ps (FZ, High, Unavailable, Good))
>      putStrLn "possible state-control sequences and their probabilities:"
>      putStrLn (showlong mxys)
>                      
>      putStrLn "computing (naively) the number of possible state-control sequences ..."
>      n <- pure (length (toList mxys))
>      putStrLn ("number of possible state-control sequences: " ++ show n)
>                      
>      putStrLn "computing (naively) the most probable state-control sequence ..."
>      xys <- pure (naiveMostProbableProb mxys)
>      putStrLn "most probable state-control sequence and its probability:"
>      putStrLn (show xys)
>      putStrLn ("reward of most probable state-control sequence: " ++ show (valStateCtrlSeq Z nSteps (fst xys)))
>                      
>      putStrLn "sorting (naively) the possible state-control sequence ..."
>      xyss <- pure (naiveSortToList mxys)
>      putStrLn "most probable state-control sequences (first 3) and their probabilities:"
>      putStrLn (showlong (take 3 xyss))
>      
>      mvs <- pure (possibleRewards' mxys)
>      putStrLn "measure of possible rewards:"
>      putStrLn ("  " ++ show (meas mvs))
>                                      
>      putStrLn "done!"
> ---}

> --{-
> lala : Nat -> { [STDIO] } Eff ()
> lala nSteps = 
>   do putStrLn "computing optimal policies ..."
>      ps <- pure (tabTailRecursiveBackwardsInduction Z nSteps)
>                     
>      putStrLn "computing possible state-control sequences ..."
>      mxys <- pure (adHocPossibleStateCtrlSeqs ps (FZ, High, Unavailable, Good))
>      putStrLn "possible state-control sequences and their probabilities:"
>      putStrLn (showlong mxys)
>                      
>      putStrLn "computing (naively) the number of possible state-control sequences ..."
>      n <- pure (length (toList mxys))
>      putStrLn ("number of possible state-control sequences: " ++ show n)
>                      
>      putStrLn "computing (naively) the most probable state-control sequence ..."
>      xys <- pure (naiveMostProbableProb mxys)
>      putStrLn "most probable state-control sequence and its probability:"
>      putStrLn (show xys)
>      putStrLn ("reward of most probable state-control sequence: " ++ show (valStateCtrlSeq Z nSteps (fst xys)))
>                      
>      putStrLn "sorting (naively) the possible state-control sequence ..."
>      xyss <- pure (naiveSortToList mxys)
>      putStrLn "most probable state-control sequences (first 3) and their probabilities:"
>      putStrLn (showlong (take 3 xyss))
>      
>      mvs <- pure (possibleRewards' mxys)
>      putStrLn "measure of possible rewards:"
>      putStrLn ("  " ++ show (meas mvs))
>                                      
>      putStrLn "done!"

> computation : { [STDIO] } Eff ()
> computation =
>   do putStr ("enter number of steps:\n")
>      nSteps <- getNat
>      case (0 == 1) of
>        False => do lala nSteps
>        True  => do putStrLn "done!"
> ---}

> main : IO ()
> main = run computation


> {-

> ---}


-- Local Variables:
-- idris-packages: ("effects")
-- End:
