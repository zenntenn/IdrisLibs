> module SequentialDecisionProblems.applications.Main

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


* Introduction

We specify a second emissions game as a stochastic sequential decision
problem with a single decision maker.

The idea is that "best" decisions on levels of greenhouse gases (GHG)
emissions (that is, how much GHG shall be allowed to be emitted in a
given time period) are affected by three major sources of uncertainty:

1) uncertainty about the (typically negative) effects of high GHG
concentrations in the atmosphere,

2) uncertainty about the availability of effective (cheap, efficient)
technologies for reducing GHG emissions,

3) uncertainty about the capability of actually implementing a decision
on a given GHG emission level.

We study the effects of 1), 2) and 3) on optimal sequences of emission
policies. The idea is to design an emission game that accounts for all
three sources of uncertainty and yet is simple enough to support
investigating the logical consequences of different assumptions through
comparisons and parametric studies.


* Controls

We consider a game in which, at each decision step, the decision maker
can select between low and high GHG emissions

> SequentialDecisionProblems.CoreTheory.Ctrl _ _ = LowHigh

Low emissions, if implemented, increase the cumulated GHG emissions less
than high emissions.


* States

At each decision step, the decision maker has to choose an option on the
basis of four data: the cumulated GHG emissions, the current emission
level (low or high), the availability of effective technologies for
reducing GHG emissions and the state of the world. Effective
technologies for reducing GHG emissions can be either available or
unavailable. The state of the world can be either good or bad:

> CumulatedEmissions : (t : Nat) -> Type
> CumulatedEmissions t = Fin (S t)

> SequentialDecisionProblems.CoreTheory.State t 
> = (CumulatedEmissions t, LowHigh, AvailableUnavailable, GoodBad)

The idea is that the game starts with zero cumulated emissions, high
emission levels, unavailable GHG technologies and with the world in a
good state. 

In these conditions, the probability to turn to the bad state is
low. But if the cumulated emissions increase beyond a fixed critical
threshold, the probability that the state of the world turns bad
increases. If the world is the bad state, there is no chance to come
back to the good state.

Similarly, the probability that effective technologies for reducing GHG
emissions become available increases after a fixed number of decision
steps. Once available, effective technologies stay available for ever.

The capability of actually implementing a decision on a given GHG
emission level in general depends on many factors. In our simplified
setup, we just investigate the effect of inertia: implementing low
emissions is easier when low emission policies are already in place than
when the current emission policies are high emission
policies. Similarly, implementing high emission policies is easier under
high emissions policies than under low emissions policies.


* Transition function

> -- The critical cumulated emissions threshold
> crE : Double
> crE = 4.0

> -- The critical number of decision steps
> crN : Nat
> crN = 2

> -- The probability of staying in a good world when the cumulated
> -- emissions are |<=| the critical threshold |crE|
> pS1  :  NonNegDouble
> pS1  =  cast 0.9 -- cast 0.8 -- cast 1.0 -- cast 0.9

> -- The probability of staying in a good world when the cumulated
> -- emissions are |>=| the critical threshold |crE|
> pS2  :  NonNegDouble
> pS2  =  cast 0.1 -- cast 0.2 -- cast 0.0 -- cast 0.1

> -- Sanity check
> pS2LTEpS1 : pS2 `NonNegDouble.Predicates.LTE` pS1
> pS2LTEpS1 = MkLTE Oh

> -- The probability of effective technologies for reducing GHG
> -- emissions becoming available when the number of decision steps is
> -- below |crN|
> pA1  :  NonNegDouble
> pA1  =  cast 0.1 -- cast 0.0 -- cast 0.1

> -- The probability of effective technologies for reducing GHG
> -- emissions becoming available when the number of decision steps is
> -- above |crN|
> pA2  :  NonNegDouble
> pA2  =  cast 0.9 -- cast 1.0 -- cast 0.9

> -- Sanity check
> pA1LTEpA2 : pA1 `NonNegDouble.Predicates.LTE` pA2
> pA1LTEpA2 = MkLTE Oh

> -- The probability being able to implement low emission policies when
> -- the current emissions are low and low emissions are selected
> pLL  :  NonNegDouble
> pLL  =  cast 0.9 -- cast 1.0 -- cast 0.9 -- cast 0.5

> -- The probability being able to implement low emission policies when
> -- the current emissions are high and low emissions are selected
> pLH  :  NonNegDouble
> pLH  =  cast 0.7 -- cast 1.0 -- cast 0.7 -- cast 0.5

> -- Sanity check
> pLHLTEpLL : pLH `NonNegDouble.Predicates.LTE` pLL
> pLHLTEpLL = MkLTE Oh

> -- The probability being able to implement high emission policies when
> -- the current emissions are low and high emissions are selected
> pHL  :  NonNegDouble
> pHL  =  cast 0.7 -- cast 1.0 -- cast 0.7 -- cast 0.5

> -- The probability being able to implement high emission policies when
> -- the current emissions are high and high emissions are selected
> pHH  :  NonNegDouble
> pHH  =  cast 0.9 -- cast 1.0 -- cast 0.9 -- cast 0.5

> -- Sanity check
> pHLLTEpHH : pHL `NonNegDouble.Predicates.LTE` pHH
> pHLLTEpHH = MkLTE Oh

Low emissions leave the cumulated emissions unchanged, high emissions
increase the cumulated emissions by one:

> -- The transition function:
>
> -- The transition function: high emissions
>
> -- The transition function: high emissions, unavailable GHG technologies
>
> -- The transition function: high emissions, unavailable GHG technologies, good world
> 
> using implementation NumNonNegDouble
>   
>   SequentialDecisionProblems.CoreTheory.nexts t (e, High, Unavailable, Good) Low =
>     let ttres = mkSimpleProb 
>                 [((weaken e, Low,  Unavailable, Good),        pLH  * (one - pA1) *        pS1), 
>                  ((    FS e, High, Unavailable, Good), (one - pLH) * (one - pA1) *        pS1),
>                  ((weaken e, Low,    Available, Good),        pLH  *        pA1  *        pS1), 
>                  ((    FS e, High,   Available, Good), (one - pLH) *        pA1  *        pS1),
>                  ((weaken e, Low,  Unavailable,  Bad),        pLH  * (one - pA1) * (one - pS1)), 
>                  ((    FS e, High, Unavailable,  Bad), (one - pLH) * (one - pA1) * (one - pS1)),
>                  ((weaken e, Low,    Available,  Bad),        pLH  *        pA1  * (one - pS1)), 
>                  ((    FS e, High,   Available,  Bad), (one - pLH) *        pA1  * (one - pS1))] in
>     let tfres = mkSimpleProb 
>                 [((weaken e, Low,  Unavailable, Good),        pLH  * (one - pA1) *        pS2), 
>                  ((    FS e, High, Unavailable, Good), (one - pLH) * (one - pA1) *        pS2),
>                  ((weaken e, Low,    Available, Good),        pLH  *        pA1  *        pS2), 
>                  ((    FS e, High,   Available, Good), (one - pLH) *        pA1  *        pS2),
>                  ((weaken e, Low,  Unavailable,  Bad),        pLH  * (one - pA1) * (one - pS2)), 
>                  ((    FS e, High, Unavailable,  Bad), (one - pLH) * (one - pA1) * (one - pS2)),
>                  ((weaken e, Low,    Available,  Bad),        pLH  *        pA1  * (one - pS2)), 
>                  ((    FS e, High,   Available,  Bad), (one - pLH) *        pA1  * (one - pS2))] in
>     let ftres = mkSimpleProb 
>                 [((weaken e, Low,  Unavailable, Good),        pLH  * (one - pA2) *        pS1), 
>                  ((    FS e, High, Unavailable, Good), (one - pLH) * (one - pA2) *        pS1),
>                  ((weaken e, Low,    Available, Good),        pLH  *        pA2  *        pS1), 
>                  ((    FS e, High,   Available, Good), (one - pLH) *        pA2  *        pS1),
>                  ((weaken e, Low,  Unavailable,  Bad),        pLH  * (one - pA2) * (one - pS1)), 
>                  ((    FS e, High, Unavailable,  Bad), (one - pLH) * (one - pA2) * (one - pS1)),
>                  ((weaken e, Low,    Available,  Bad),        pLH  *        pA2  * (one - pS1)), 
>                  ((    FS e, High,   Available,  Bad), (one - pLH) *        pA2  * (one - pS1))] in
>     let ffres = mkSimpleProb 
>                 [((weaken e, Low,  Unavailable, Good),        pLH  * (one - pA2) *        pS2), 
>                  ((    FS e, High, Unavailable, Good), (one - pLH) * (one - pA2) *        pS2),
>                  ((weaken e, Low,    Available, Good),        pLH  *        pA2  *        pS2), 
>                  ((    FS e, High,   Available, Good), (one - pLH) *        pA2  *        pS2),
>                  ((weaken e, Low,  Unavailable,  Bad),        pLH  * (one - pA2) * (one - pS2)), 
>                  ((    FS e, High, Unavailable,  Bad), (one - pLH) * (one - pA2) * (one - pS2)),
>                  ((weaken e, Low,    Available,  Bad),        pLH  *        pA2  * (one - pS2)), 
>                  ((    FS e, High,   Available,  Bad), (one - pLH) *        pA2  * (one - pS2))] in
>     case (t <= crN) of
>       True  =>   case (fromFin e <= crE) of
>                  True  =>   trim ttres
>                  False =>   trim tfres
>       False =>   case (fromFin e <= crE) of
>                  True  =>   trim ftres
>                  False =>   trim ffres
>   SequentialDecisionProblems.CoreTheory.nexts t (e, High, Unavailable, Good) High =
>     let ttres = mkSimpleProb 
>                 [((weaken e, Low,  Unavailable, Good), (one - pHH) * (one - pA1) *        pS1), 
>                  ((    FS e, High, Unavailable, Good),        pHH  * (one - pA1) *        pS1),
>                  ((weaken e, Low,    Available, Good), (one - pHH) *        pA1  *        pS1), 
>                  ((    FS e, High,   Available, Good),        pHH  *        pA1  *        pS1),
>                  ((weaken e, Low,  Unavailable,  Bad), (one - pHH) * (one - pA1) * (one - pS1)), 
>                  ((    FS e, High, Unavailable,  Bad),        pHH  * (one - pA1) * (one - pS1)),
>                  ((weaken e, Low,    Available,  Bad), (one - pHH) *        pA1  * (one - pS1)), 
>                  ((    FS e, High,   Available,  Bad),        pHH  *        pA1  * (one - pS1))] in
>     let tfres = mkSimpleProb 
>                 [((weaken e, Low,  Unavailable, Good), (one - pHH) * (one - pA1) *        pS2), 
>                  ((    FS e, High, Unavailable, Good),        pHH  * (one - pA1) *        pS2),
>                  ((weaken e, Low,    Available, Good), (one - pHH) *        pA1  *        pS2), 
>                  ((    FS e, High,   Available, Good),        pHH  *        pA1  *        pS2),
>                  ((weaken e, Low,  Unavailable,  Bad), (one - pHH) * (one - pA1) * (one - pS2)), 
>                  ((    FS e, High, Unavailable,  Bad),        pHH  * (one - pA1) * (one - pS2)),
>                  ((weaken e, Low,    Available,  Bad), (one - pHH) *        pA1  * (one - pS2)), 
>                  ((    FS e, High,   Available,  Bad),        pHH  *        pA1  * (one - pS2))] in
>     let ftres = mkSimpleProb 
>                 [((weaken e, Low,  Unavailable, Good), (one - pHH) * (one - pA2) *        pS1), 
>                  ((    FS e, High, Unavailable, Good),        pHH  * (one - pA2) *        pS1),
>                  ((weaken e, Low,    Available, Good), (one - pHH) *        pA2  *        pS1), 
>                  ((    FS e, High,   Available, Good),        pHH  *        pA2  *        pS1),
>                  ((weaken e, Low,  Unavailable,  Bad), (one - pHH) * (one - pA2) * (one - pS1)), 
>                  ((    FS e, High, Unavailable,  Bad),        pHH  * (one - pA2) * (one - pS1)),
>                  ((weaken e, Low,    Available,  Bad), (one - pHH) *        pA2  * (one - pS1)), 
>                  ((    FS e, High,   Available,  Bad),        pHH  *        pA2  * (one - pS1))] in
>     let ffres = mkSimpleProb 
>                 [((weaken e, Low,  Unavailable, Good), (one - pHH) * (one - pA2) *        pS2), 
>                  ((    FS e, High, Unavailable, Good),        pHH  * (one - pA2) *        pS2),
>                  ((weaken e, Low,    Available, Good), (one - pHH) *        pA2  *        pS2), 
>                  ((    FS e, High,   Available, Good),        pHH  *        pA2  *        pS2),
>                  ((weaken e, Low,  Unavailable,  Bad), (one - pHH) * (one - pA2) * (one - pS2)), 
>                  ((    FS e, High, Unavailable,  Bad),        pHH  * (one - pA2) * (one - pS2)),
>                  ((weaken e, Low,    Available,  Bad), (one - pHH) *        pA2  * (one - pS2)), 
>                  ((    FS e, High,   Available,  Bad),        pHH  *        pA2  * (one - pS2))] in
>     case (t <= crN) of
>       True  =>   case (fromFin e <= crE) of
>                  True  =>   trim ttres
>                  False =>   trim tfres
>       False =>   case (fromFin e <= crE) of
>                  True  =>   trim ftres
>                  False =>   trim ffres
>
>   -- The transition function: high emissions, unavailable GHG technologies, bad world
>   SequentialDecisionProblems.CoreTheory.nexts t (e, High, Unavailable, Bad) Low =
>     let ttres = mkSimpleProb 
>                 [((weaken e, Low,  Unavailable,  Bad),        pLH  * (one - pA1)), 
>                  ((    FS e, High, Unavailable,  Bad), (one - pLH) * (one - pA1)),
>                  ((weaken e, Low,    Available,  Bad),        pLH  *        pA1 ), 
>                  ((    FS e, High,   Available,  Bad), (one - pLH) *        pA1 )] in
>     let tfres = mkSimpleProb 
>                 [((weaken e, Low,  Unavailable,  Bad),        pLH  * (one - pA1)), 
>                  ((    FS e, High, Unavailable,  Bad), (one - pLH) * (one - pA1)),
>                  ((weaken e, Low,    Available,  Bad),        pLH  *        pA1 ), 
>                  ((    FS e, High,   Available,  Bad), (one - pLH) *        pA1 )] in
>     let ftres = mkSimpleProb 
>                 [((weaken e, Low,  Unavailable,  Bad),        pLH  * (one - pA2)), 
>                  ((    FS e, High, Unavailable,  Bad), (one - pLH) * (one - pA2)),
>                  ((weaken e, Low,    Available,  Bad),        pLH  *        pA2 ), 
>                  ((    FS e, High,   Available,  Bad), (one - pLH) *        pA2 )] in
>     let ffres = mkSimpleProb 
>                 [((weaken e, Low,  Unavailable,  Bad),        pLH  * (one - pA2)), 
>                  ((    FS e, High, Unavailable,  Bad), (one - pLH) * (one - pA2)),
>                  ((weaken e, Low,    Available,  Bad),        pLH  *        pA2 ), 
>                  ((    FS e, High,   Available,  Bad), (one - pLH) *        pA2 )] in
>     case (t <= crN) of
>       True  =>   case (fromFin e <= crE) of
>                  True  =>   trim ttres
>                  False =>   trim tfres
>       False =>   case (fromFin e <= crE) of
>                  True  =>   trim ftres
>                  False =>   trim ffres
>   SequentialDecisionProblems.CoreTheory.nexts t (e, High, Unavailable, Bad) High =
>     let ttres = mkSimpleProb 
>                 [((weaken e, Low,  Unavailable,  Bad), (one - pHH) * (one - pA1)), 
>                  ((    FS e, High, Unavailable,  Bad),        pHH  * (one - pA1)),
>                  ((weaken e, Low,    Available,  Bad), (one - pHH) *        pA1 ), 
>                  ((    FS e, High,   Available,  Bad),        pHH  *        pA1 )] in
>     let tfres = mkSimpleProb 
>                 [((weaken e, Low,  Unavailable,  Bad), (one - pHH) * (one - pA1)), 
>                  ((    FS e, High, Unavailable,  Bad),        pHH  * (one - pA1)),
>                  ((weaken e, Low,    Available,  Bad), (one - pHH) *        pA1 ), 
>                  ((    FS e, High,   Available,  Bad),        pHH  *        pA1 )] in
>     let ftres = mkSimpleProb 
>                 [((weaken e, Low,  Unavailable,  Bad), (one - pHH) * (one - pA2)), 
>                  ((    FS e, High, Unavailable,  Bad),        pHH  * (one - pA2)),
>                  ((weaken e, Low,    Available,  Bad), (one - pHH) *        pA2 ), 
>                  ((    FS e, High,   Available,  Bad),        pHH  *        pA2 )] in
>     let ffres = mkSimpleProb 
>                 [((weaken e, Low,  Unavailable,  Bad), (one - pHH) * (one - pA2)), 
>                  ((    FS e, High, Unavailable,  Bad),        pHH  * (one - pA2)),
>                  ((weaken e, Low,    Available,  Bad), (one - pHH) *        pA2 ), 
>                  ((    FS e, High,   Available,  Bad),        pHH  *        pA2 )] in
>     case (t <= crN) of
>       True  =>   case (fromFin e <= crE) of
>                  True  =>   trim ttres
>                  False =>   trim tfres
>       False =>   case (fromFin e <= crE) of
>                  True  =>   trim ftres
>                  False =>   trim ffres
>
>
>   -- The transition function: high emissions, available GHG technologies
>
>   -- The transition function: high emissions, available GHG technologies, good world
>   SequentialDecisionProblems.CoreTheory.nexts t (e, High, Available, Good) Low =
>     let ttres = mkSimpleProb 
>                 [((weaken e, Low,    Available, Good),        pLH  *        pS1), 
>                  ((    FS e, High,   Available, Good), (one - pLH) *        pS1),
>                  ((weaken e, Low,    Available,  Bad),        pLH  * (one - pS1)), 
>                  ((    FS e, High,   Available,  Bad), (one - pLH) * (one - pS1))] in
>     let tfres = mkSimpleProb 
>                 [((weaken e, Low,    Available, Good),        pLH  *        pS2), 
>                  ((    FS e, High,   Available, Good), (one - pLH) *        pS2),
>                  ((weaken e, Low,    Available,  Bad),        pLH  * (one - pS2)), 
>                  ((    FS e, High,   Available,  Bad), (one - pLH) * (one - pS2))] in
>     let ftres = mkSimpleProb 
>                 [((weaken e, Low,    Available, Good),        pLH  *        pS1), 
>                  ((    FS e, High,   Available, Good), (one - pLH) *        pS1),
>                  ((weaken e, Low,    Available,  Bad),        pLH  * (one - pS1)), 
>                  ((    FS e, High,   Available,  Bad), (one - pLH) * (one - pS1))] in
>     let ffres = mkSimpleProb 
>                 [((weaken e, Low,    Available, Good),        pLH  *        pS2), 
>                  ((    FS e, High,   Available, Good), (one - pLH) *        pS2),
>                  ((weaken e, Low,    Available,  Bad),        pLH  * (one - pS2)), 
>                  ((    FS e, High,   Available,  Bad), (one - pLH) * (one - pS2))] in
>     case (t <= crN) of
>       True  =>   case (fromFin e <= crE) of
>                  True  =>   trim ttres
>                  False =>   trim tfres
>       False =>   case (fromFin e <= crE) of
>                  True  =>   trim ftres
>                  False =>   trim ffres
>   SequentialDecisionProblems.CoreTheory.nexts t (e, High, Available, Good) High =
>     let ttres = mkSimpleProb 
>                 [((weaken e, Low,    Available, Good), (one - pHH) *        pS1), 
>                  ((    FS e, High,   Available, Good),        pHH  *        pS1),
>                  ((weaken e, Low,    Available,  Bad), (one - pHH) * (one - pS1)), 
>                  ((    FS e, High,   Available,  Bad),        pHH  * (one - pS1))] in
>     let tfres = mkSimpleProb 
>                 [((weaken e, Low,    Available, Good), (one - pHH) *        pS2), 
>                  ((    FS e, High,   Available, Good),        pHH  *        pS2),
>                  ((weaken e, Low,    Available,  Bad), (one - pHH) * (one - pS2)), 
>                  ((    FS e, High,   Available,  Bad),        pHH  * (one - pS2))] in
>     let ftres = mkSimpleProb 
>                 [((weaken e, Low,    Available, Good), (one - pHH) *        pS1), 
>                  ((    FS e, High,   Available, Good),        pHH  *        pS1),
>                  ((weaken e, Low,    Available,  Bad), (one - pHH) * (one - pS1)), 
>                  ((    FS e, High,   Available,  Bad),        pHH  * (one - pS1))] in
>     let ffres = mkSimpleProb 
>                 [((weaken e, Low,    Available, Good), (one - pHH) *        pS2), 
>                  ((    FS e, High,   Available, Good),        pHH  *        pS2),
>                  ((weaken e, Low,    Available,  Bad), (one - pHH) * (one - pS2)), 
>                  ((    FS e, High,   Available,  Bad),        pHH  * (one - pS2))] in
>     case (t <= crN) of
>       True  =>   case (fromFin e <= crE) of
>                  True  =>   trim ttres
>                  False =>   trim tfres
>       False =>   case (fromFin e <= crE) of
>                  True  =>   trim ftres
>                  False =>   trim ffres
>
>   -- The transition function: high emissions, available GHG technologies, bad world
>   SequentialDecisionProblems.CoreTheory.nexts t (e, High, Available, Bad) Low =
>     let ttres = mkSimpleProb 
>                 [((weaken e, Low,    Available,  Bad),        pLH ), 
>                  ((    FS e, High,   Available,  Bad), (one - pLH))] in
>     let tfres = mkSimpleProb 
>                 [((weaken e, Low,    Available,  Bad),        pLH ), 
>                  ((    FS e, High,   Available,  Bad), (one - pLH))] in
>     let ftres = mkSimpleProb 
>                 [((weaken e, Low,    Available,  Bad),        pLH ), 
>                  ((    FS e, High,   Available,  Bad), (one - pLH))] in
>     let ffres = mkSimpleProb 
>                 [((weaken e, Low,    Available,  Bad),        pLH ), 
>                  ((    FS e, High,   Available,  Bad), (one - pLH))] in
>     case (t <= crN) of
>       True  =>   case (fromFin e <= crE) of
>                  True  =>   trim ttres
>                  False =>   trim tfres
>       False =>   case (fromFin e <= crE) of
>                  True  =>   trim ftres
>                  False =>   trim ffres
>   SequentialDecisionProblems.CoreTheory.nexts t (e, High, Available, Bad) High =
>     let ttres = mkSimpleProb 
>                 [((weaken e, Low,    Available,  Bad), (one - pHH)), 
>                  ((    FS e, High,   Available,  Bad),        pHH )] in
>     let tfres = mkSimpleProb 
>                 [((weaken e, Low,    Available,  Bad), (one - pHH)), 
>                  ((    FS e, High,   Available,  Bad),        pHH )] in
>     let ftres = mkSimpleProb 
>                 [((weaken e, Low,    Available,  Bad), (one - pHH)), 
>                  ((    FS e, High,   Available,  Bad),        pHH )] in
>     let ffres = mkSimpleProb 
>                 [((weaken e, Low,    Available,  Bad), (one - pHH)), 
>                  ((    FS e, High,   Available,  Bad),        pHH )] in
>     case (t <= crN) of
>       True  =>   case (fromFin e <= crE) of
>                  True  =>   trim ttres
>                  False =>   trim tfres
>       False =>   case (fromFin e <= crE) of
>                  True  =>   trim ftres
>                  False =>   trim ffres
>
>
>
>
>   -- The transition function: low emissions
>
>   -- The transition function: low emissions, unavailable GHG technologies
>
>   -- The transition function: low emissions, unavailable GHG technologies, good world
>   SequentialDecisionProblems.CoreTheory.nexts t (e, Low, Unavailable, Good) Low =
>     let ttres = mkSimpleProb 
>                 [((weaken e, Low,  Unavailable, Good),        pLL  * (one - pA1) *        pS1), 
>                  ((    FS e, High, Unavailable, Good), (one - pLL) * (one - pA1) *        pS1),
>                  ((weaken e, Low,    Available, Good),        pLL  *        pA1  *        pS1), 
>                  ((    FS e, High,   Available, Good), (one - pLL) *        pA1  *        pS1),
>                  ((weaken e, Low,  Unavailable,  Bad),        pLL  * (one - pA1) * (one - pS1)), 
>                  ((    FS e, High, Unavailable,  Bad), (one - pLL) * (one - pA1) * (one - pS1)),
>                  ((weaken e, Low,    Available,  Bad),        pLL  *        pA1  * (one - pS1)), 
>                  ((    FS e, High,   Available,  Bad), (one - pLL) *        pA1  * (one - pS1))] in
>     let tfres = mkSimpleProb 
>                 [((weaken e, Low,  Unavailable, Good),        pLL  * (one - pA1) *        pS2), 
>                  ((    FS e, High, Unavailable, Good), (one - pLL) * (one - pA1) *        pS2),
>                  ((weaken e, Low,    Available, Good),        pLL  *        pA1  *        pS2), 
>                  ((    FS e, High,   Available, Good), (one - pLL) *        pA1  *        pS2),
>                  ((weaken e, Low,  Unavailable,  Bad),        pLL  * (one - pA1) * (one - pS2)), 
>                  ((    FS e, High, Unavailable,  Bad), (one - pLL) * (one - pA1) * (one - pS2)),
>                  ((weaken e, Low,    Available,  Bad),        pLL  *        pA1  * (one - pS2)), 
>                  ((    FS e, High,   Available,  Bad), (one - pLL) *        pA1  * (one - pS2))] in
>     let ftres = mkSimpleProb 
>                 [((weaken e, Low,  Unavailable, Good),        pLL  * (one - pA2) *        pS1), 
>                  ((    FS e, High, Unavailable, Good), (one - pLL) * (one - pA2) *        pS1),
>                  ((weaken e, Low,    Available, Good),        pLL  *        pA2  *        pS1), 
>                  ((    FS e, High,   Available, Good), (one - pLL) *        pA2  *        pS1),
>                  ((weaken e, Low,  Unavailable,  Bad),        pLL  * (one - pA2) * (one - pS1)), 
>                  ((    FS e, High, Unavailable,  Bad), (one - pLL) * (one - pA2) * (one - pS1)),
>                  ((weaken e, Low,    Available,  Bad),        pLL  *        pA2  * (one - pS1)), 
>                  ((    FS e, High,   Available,  Bad), (one - pLL) *        pA2  * (one - pS1))] in
>     let ffres = mkSimpleProb 
>                 [((weaken e, Low,  Unavailable, Good),        pLL  * (one - pA2) *        pS2), 
>                  ((    FS e, High, Unavailable, Good), (one - pLL) * (one - pA2) *        pS2),
>                  ((weaken e, Low,    Available, Good),        pLL  *        pA2  *        pS2), 
>                  ((    FS e, High,   Available, Good), (one - pLL) *        pA2  *        pS2),
>                  ((weaken e, Low,  Unavailable,  Bad),        pLL  * (one - pA2) * (one - pS2)), 
>                  ((    FS e, High, Unavailable,  Bad), (one - pLL) * (one - pA2) * (one - pS2)),
>                  ((weaken e, Low,    Available,  Bad),        pLL  *        pA2  * (one - pS2)), 
>                  ((    FS e, High,   Available,  Bad), (one - pLL) *        pA2  * (one - pS2))] in
>     case (t <= crN) of
>       True  =>   case (fromFin e <= crE) of
>                  True  =>   trim ttres
>                  False =>   trim tfres
>       False =>   case (fromFin e <= crE) of
>                  True  =>   trim ftres
>                  False =>   trim ffres
>   SequentialDecisionProblems.CoreTheory.nexts t (e, Low, Unavailable, Good) High =
>     let ttres = mkSimpleProb 
>                 [((weaken e, Low,  Unavailable, Good), (one - pHL) * (one - pA1) *        pS1), 
>                  ((    FS e, High, Unavailable, Good),        pHL  * (one - pA1) *        pS1),
>                  ((weaken e, Low,    Available, Good), (one - pHL) *        pA1  *        pS1), 
>                  ((    FS e, High,   Available, Good),        pHL  *        pA1  *        pS1),
>                  ((weaken e, Low,  Unavailable,  Bad), (one - pHL) * (one - pA1) * (one - pS1)), 
>                  ((    FS e, High, Unavailable,  Bad),        pHL  * (one - pA1) * (one - pS1)),
>                  ((weaken e, Low,    Available,  Bad), (one - pHL) *        pA1  * (one - pS1)), 
>                  ((    FS e, High,   Available,  Bad),        pHL  *        pA1  * (one - pS1))] in
>     let tfres = mkSimpleProb 
>                 [((weaken e, Low,  Unavailable, Good), (one - pHL) * (one - pA1) *        pS2), 
>                  ((    FS e, High, Unavailable, Good),        pHL  * (one - pA1) *        pS2),
>                  ((weaken e, Low,    Available, Good), (one - pHL) *        pA1  *        pS2), 
>                  ((    FS e, High,   Available, Good),        pHL  *        pA1  *        pS2),
>                  ((weaken e, Low,  Unavailable,  Bad), (one - pHL) * (one - pA1) * (one - pS2)), 
>                  ((    FS e, High, Unavailable,  Bad),        pHL  * (one - pA1) * (one - pS2)),
>                  ((weaken e, Low,    Available,  Bad), (one - pHL) *        pA1  * (one - pS2)), 
>                  ((    FS e, High,   Available,  Bad),        pHL  *        pA1  * (one - pS2))] in
>     let ftres = mkSimpleProb 
>                 [((weaken e, Low,  Unavailable, Good), (one - pHL) * (one - pA2) *        pS1), 
>                  ((    FS e, High, Unavailable, Good),        pHL  * (one - pA2) *        pS1),
>                  ((weaken e, Low,    Available, Good), (one - pHL) *        pA2  *        pS1), 
>                  ((    FS e, High,   Available, Good),        pHL  *        pA2  *        pS1),
>                  ((weaken e, Low,  Unavailable,  Bad), (one - pHL) * (one - pA2) * (one - pS1)), 
>                  ((    FS e, High, Unavailable,  Bad),        pHL  * (one - pA2) * (one - pS1)),
>                  ((weaken e, Low,    Available,  Bad), (one - pHL) *        pA2  * (one - pS1)), 
>                  ((    FS e, High,   Available,  Bad),        pHL  *        pA2  * (one - pS1))] in
>     let ffres = mkSimpleProb 
>                 [((weaken e, Low,  Unavailable, Good), (one - pHL) * (one - pA2) *        pS2), 
>                  ((    FS e, High, Unavailable, Good),        pHL  * (one - pA2) *        pS2),
>                  ((weaken e, Low,    Available, Good), (one - pHL) *        pA2  *        pS2), 
>                  ((    FS e, High,   Available, Good),        pHL  *        pA2  *        pS2),
>                  ((weaken e, Low,  Unavailable,  Bad), (one - pHL) * (one - pA2) * (one - pS2)), 
>                  ((    FS e, High, Unavailable,  Bad),        pHL  * (one - pA2) * (one - pS2)),
>                  ((weaken e, Low,    Available,  Bad), (one - pHL) *        pA2  * (one - pS2)), 
>                  ((    FS e, High,   Available,  Bad),        pHL  *        pA2  * (one - pS2))] in
>     case (t <= crN) of
>       True  =>   case (fromFin e <= crE) of
>                  True  =>   trim ttres
>                  False =>   trim tfres
>       False =>   case (fromFin e <= crE) of
>                  True  =>   trim ftres
>                  False =>   trim ffres
>
>   -- The transition function: low emissions, unavailable GHG technologies, bad world
>   SequentialDecisionProblems.CoreTheory.nexts t (e, Low, Unavailable, Bad) Low =
>     let ttres = mkSimpleProb 
>                 [((weaken e, Low,  Unavailable,  Bad),        pLL  * (one - pA1)), 
>                  ((    FS e, High, Unavailable,  Bad), (one - pLL) * (one - pA1)),
>                  ((weaken e, Low,    Available,  Bad),        pLL  *        pA1 ), 
>                  ((    FS e, High,   Available,  Bad), (one - pLL) *        pA1 )] in
>     let tfres = mkSimpleProb 
>                 [((weaken e, Low,  Unavailable,  Bad),        pLL  * (one - pA1)), 
>                  ((    FS e, High, Unavailable,  Bad), (one - pLL) * (one - pA1)),
>                  ((weaken e, Low,    Available,  Bad),        pLL  *        pA1 ), 
>                  ((    FS e, High,   Available,  Bad), (one - pLL) *        pA1 )] in
>     let ftres = mkSimpleProb 
>                 [((weaken e, Low,  Unavailable,  Bad),        pLL  * (one - pA2)), 
>                  ((    FS e, High, Unavailable,  Bad), (one - pLL) * (one - pA2)),
>                  ((weaken e, Low,    Available,  Bad),        pLL  *        pA2 ), 
>                  ((    FS e, High,   Available,  Bad), (one - pLL) *        pA2 )] in
>     let ffres = mkSimpleProb 
>                 [((weaken e, Low,  Unavailable,  Bad),        pLL  * (one - pA2)), 
>                  ((    FS e, High, Unavailable,  Bad), (one - pLL) * (one - pA2)),
>                  ((weaken e, Low,    Available,  Bad),        pLL  *        pA2 ), 
>                  ((    FS e, High,   Available,  Bad), (one - pLL) *        pA2 )] in
>     case (t <= crN) of
>       True  =>   case (fromFin e <= crE) of
>                  True  =>   trim ttres
>                  False =>   trim tfres
>       False =>   case (fromFin e <= crE) of
>                  True  =>   trim ftres
>                  False =>   trim ffres
>   SequentialDecisionProblems.CoreTheory.nexts t (e, Low, Unavailable, Bad) High =
>     let ttres = mkSimpleProb 
>                 [((weaken e, Low,  Unavailable,  Bad), (one - pHL) * (one - pA1)), 
>                  ((    FS e, High, Unavailable,  Bad),        pHL  * (one - pA1)),
>                  ((weaken e, Low,    Available,  Bad), (one - pHL) *        pA1 ), 
>                  ((    FS e, High,   Available,  Bad),        pHL  *        pA1 )] in
>     let tfres = mkSimpleProb 
>                 [((weaken e, Low,  Unavailable,  Bad), (one - pHL) * (one - pA1)), 
>                  ((    FS e, High, Unavailable,  Bad),        pHL  * (one - pA1)),
>                  ((weaken e, Low,    Available,  Bad), (one - pHL) *        pA1 ), 
>                  ((    FS e, High,   Available,  Bad),        pHL  *        pA1 )] in
>     let ftres = mkSimpleProb 
>                 [((weaken e, Low,  Unavailable,  Bad), (one - pHL) * (one - pA2)), 
>                  ((    FS e, High, Unavailable,  Bad),        pHL  * (one - pA2)),
>                  ((weaken e, Low,    Available,  Bad), (one - pHL) *        pA2 ), 
>                  ((    FS e, High,   Available,  Bad),        pHL  *        pA2 )] in
>     let ffres = mkSimpleProb 
>                 [((weaken e, Low,  Unavailable,  Bad), (one - pHL) * (one - pA2)), 
>                  ((    FS e, High, Unavailable,  Bad),        pHL  * (one - pA2)),
>                  ((weaken e, Low,    Available,  Bad), (one - pHL) *        pA2 ), 
>                  ((    FS e, High,   Available,  Bad),        pHL  *        pA2 )] in
>     case (t <= crN) of
>       True  =>   case (fromFin e <= crE) of
>                  True  =>   trim ttres
>                  False =>   trim tfres
>       False =>   case (fromFin e <= crE) of
>                  True  =>   trim ftres
>                  False =>   trim ffres
>
>
>   -- The transition function: low emissions, available GHG technologies
>
>   -- The transition function: low emissions, available GHG technologies, good world
>   SequentialDecisionProblems.CoreTheory.nexts t (e, Low, Available, Good) Low =
>     let ttres = mkSimpleProb 
>                 [((weaken e, Low,    Available, Good),        pLL  *        pS1), 
>                  ((    FS e, High,   Available, Good), (one - pLL) *        pS1),
>                  ((weaken e, Low,    Available,  Bad),        pLL  * (one - pS1)), 
>                  ((    FS e, High,   Available,  Bad), (one - pLL) * (one - pS1))] in
>     let tfres = mkSimpleProb 
>                 [((weaken e, Low,    Available, Good),        pLL  *        pS2), 
>                  ((    FS e, High,   Available, Good), (one - pLL) *        pS2),
>                  ((weaken e, Low,    Available,  Bad),        pLL  * (one - pS2)), 
>                  ((    FS e, High,   Available,  Bad), (one - pLL) * (one - pS2))] in
>     let ftres = mkSimpleProb 
>                 [((weaken e, Low,    Available, Good),        pLL  *        pS1), 
>                  ((    FS e, High,   Available, Good), (one - pLL) *        pS1),
>                  ((weaken e, Low,    Available,  Bad),        pLL  * (one - pS1)), 
>                  ((    FS e, High,   Available,  Bad), (one - pLL) * (one - pS1))] in
>     let ffres = mkSimpleProb 
>                 [((weaken e, Low,    Available, Good),        pLL  *        pS2), 
>                  ((    FS e, High,   Available, Good), (one - pLL) *        pS2),
>                  ((weaken e, Low,    Available,  Bad),        pLL  * (one - pS2)), 
>                  ((    FS e, High,   Available,  Bad), (one - pLL) * (one - pS2))] in
>     case (t <= crN) of
>       True  =>   case (fromFin e <= crE) of
>                  True  =>   trim ttres
>                  False =>   trim tfres
>       False =>   case (fromFin e <= crE) of
>                  True  =>   trim ftres
>                  False =>   trim ffres
>   SequentialDecisionProblems.CoreTheory.nexts t (e, Low, Available, Good) High =
>     let ttres = mkSimpleProb 
>                 [((weaken e, Low,    Available, Good), (one - pHL) *        pS1), 
>                  ((    FS e, High,   Available, Good),        pHL  *        pS1),
>                  ((weaken e, Low,    Available,  Bad), (one - pHL) * (one - pS1)), 
>                  ((    FS e, High,   Available,  Bad),        pHL  * (one - pS1))] in
>     let tfres = mkSimpleProb 
>                 [((weaken e, Low,    Available, Good), (one - pHL) *        pS2), 
>                  ((    FS e, High,   Available, Good),        pHL  *        pS2),
>                  ((weaken e, Low,    Available,  Bad), (one - pHL) * (one - pS2)), 
>                  ((    FS e, High,   Available,  Bad),        pHL  * (one - pS2))] in
>     let ftres = mkSimpleProb 
>                 [((weaken e, Low,    Available, Good), (one - pHL) *        pS1), 
>                  ((    FS e, High,   Available, Good),        pHL  *        pS1),
>                  ((weaken e, Low,    Available,  Bad), (one - pHL) * (one - pS1)), 
>                  ((    FS e, High,   Available,  Bad),        pHL  * (one - pS1))] in
>     let ffres = mkSimpleProb 
>                 [((weaken e, Low,    Available, Good), (one - pHL) *        pS2), 
>                  ((    FS e, High,   Available, Good),        pHL  *        pS2),
>                  ((weaken e, Low,    Available,  Bad), (one - pHL) * (one - pS2)), 
>                  ((    FS e, High,   Available,  Bad),        pHL  * (one - pS2))] in
>     case (t <= crN) of
>       True  =>   case (fromFin e <= crE) of
>                  True  =>   trim ttres
>                  False =>   trim tfres
>       False =>   case (fromFin e <= crE) of
>                  True  =>   trim ftres
>                  False =>   trim ffres
>
>   -- The transition function: low emissions, available GHG technologies, bad world
>   SequentialDecisionProblems.CoreTheory.nexts t (e, Low, Available, Bad) Low =
>     let ttres = mkSimpleProb 
>                 [((weaken e, Low,    Available,  Bad),        pLL ), 
>                  ((    FS e, High,   Available,  Bad), (one - pLL))] in
>     let tfres = mkSimpleProb 
>                 [((weaken e, Low,    Available,  Bad),        pLL ), 
>                  ((    FS e, High,   Available,  Bad), (one - pLL))] in
>     let ftres = mkSimpleProb 
>                 [((weaken e, Low,    Available,  Bad),        pLL ), 
>                  ((    FS e, High,   Available,  Bad), (one - pLL))] in
>     let ffres = mkSimpleProb 
>                 [((weaken e, Low,    Available,  Bad),        pLL ), 
>                  ((    FS e, High,   Available,  Bad), (one - pLL))] in
>     case (t <= crN) of
>       True  =>   case (fromFin e <= crE) of
>                  True  =>   trim ttres
>                  False =>   trim tfres
>       False =>   case (fromFin e <= crE) of
>                  True  =>   trim ftres
>                  False =>   trim ffres
>   SequentialDecisionProblems.CoreTheory.nexts t (e, Low, Available, Bad) High =
>     let ttres = mkSimpleProb 
>                 [((weaken e, Low,    Available,  Bad), (one - pHL)), 
>                  ((    FS e, High,   Available,  Bad),        pHL )] in
>     let tfres = mkSimpleProb 
>                 [((weaken e, Low,    Available,  Bad), (one - pHL)), 
>                  ((    FS e, High,   Available,  Bad),        pHL )] in
>     let ftres = mkSimpleProb 
>                 [((weaken e, Low,    Available,  Bad), (one - pHL)), 
>                  ((    FS e, High,   Available,  Bad),        pHL )] in
>     let ffres = mkSimpleProb 
>                 [((weaken e, Low,    Available,  Bad), (one - pHL)), 
>                  ((    FS e, High,   Available,  Bad),        pHL )] in
>     case (t <= crN) of
>       True  =>   case (fromFin e <= crE) of
>                  True  =>   trim ttres
>                  False =>   trim tfres
>       False =>   case (fromFin e <= crE) of
>                  True  =>   trim ftres
>                  False =>   trim ffres


* |Val| and |LTE|:

> SequentialDecisionProblems.CoreTheory.Val =
>   NonNegDouble.NonNegDouble
 
> SequentialDecisionProblems.CoreTheory.plus =
>   NonNegDouble.Operations.plus

> SequentialDecisionProblems.CoreTheory.zero =
>   fromInteger @{NumNonNegDouble} 0

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

The idea is that being in a good world yields one unit of benefits per
step and being in a bad world yield less benefits:

> -- Ratio of the benefits in a bad world and the benefits in a good world
> badOverGood : NonNegDouble
> badOverGood = cast 0.89 -- cast 0.89 -- cast 0.5

> -- Sanity check
> badOverGoodLTEone : badOverGood `NonNegDouble.Predicates.LTE` one
> badOverGoodLTEone = MkLTE Oh

Emitting GHGs also brings benefits. These are a fraction of the step
benefits in a good world and low emissions bring less benefits than high
emissions:

> -- Ratio between low emissions and step benefits in good world, when
> -- effective technologies for reducing GHG emissions are unavailable
> lowOverGoodUnavailable : NonNegDouble
> lowOverGoodUnavailable = cast 0.1 -- cast 0.0 -- cast 0.1

> -- Ratio between low emissions and step benefits in good world, when
> -- effective technologies for reducing GHG emissions are available
> lowOverGoodAvailable : NonNegDouble
> lowOverGoodAvailable = cast 0.2 -- cast 0.1 -- cast 0.2

> -- Ratio between high emissions and step benefits in a good world
> highOverGood : NonNegDouble
> highOverGood = cast 0.3

> -- Sanity check
> lowOverGoodUnavailableLTEone : lowOverGoodUnavailable `NonNegDouble.Predicates.LTE` one
> lowOverGoodUnavailableLTEone = MkLTE Oh

> -- Sanity check
> lowOverGoodAvailableLTEone : lowOverGoodAvailable `NonNegDouble.Predicates.LTE` one
> lowOverGoodAvailableLTEone = MkLTE Oh

> -- Sanity check
> lowOverGoodUnavailableLTElowOverGoodAvailable : lowOverGoodUnavailable `NonNegDouble.Predicates.LTE` lowOverGoodAvailable
> lowOverGoodUnavailableLTElowOverGoodAvailable = MkLTE Oh

> -- Sanity check
> highOverGoodLTEone : highOverGood `NonNegDouble.Predicates.LTE` one
> highOverGoodLTEone = MkLTE Oh

> -- Sanity check
> lowLTEhigh : lowOverGoodAvailable `NonNegDouble.Predicates.LTE` highOverGood
> lowLTEhigh = MkLTE Oh

The reward only depend on the next state, not on the current state or on
the selected control:

> -- Reward function:
> 
> using implementation NumNonNegDouble
>   
>   SequentialDecisionProblems.CoreTheory.reward _ _ _ (e, High, Unavailable, Good) =
>     one               + one * highOverGood
>   SequentialDecisionProblems.CoreTheory.reward _ _ _ (e, High, Unavailable,  Bad) =
>     one * badOverGood + one * highOverGood
>
>   SequentialDecisionProblems.CoreTheory.reward _ _ _ (e, High,   Available, Good) =
>     one               + one * highOverGood
>   SequentialDecisionProblems.CoreTheory.reward _ _ _ (e, High,   Available,  Bad) =
>     one * badOverGood + one * highOverGood
>     
>   SequentialDecisionProblems.CoreTheory.reward _ _ _ (e,  Low, Unavailable, Good) =
>     one               + one * lowOverGoodUnavailable
>   SequentialDecisionProblems.CoreTheory.reward _ _ _ (e,  Low, Unavailable,  Bad) =
>     one * badOverGood + one * lowOverGoodUnavailable
>
>   SequentialDecisionProblems.CoreTheory.reward _ _ _ (e,  Low,   Available, Good) =
>     one               + one * lowOverGoodAvailable
>   SequentialDecisionProblems.CoreTheory.reward _ _ _ (e,  Low,   Available,  Bad) =
>     one * badOverGood + one * lowOverGoodAvailable

 
* Completing the problem specification

To be able to apply the verified, generic backwards induction algorithm
of |CoreTheory| to compute optimal policies for our problem, we have to
explain how the decision maker accounts for uncertainties on rewards
induced by uncertainties in the transition function. We first assume
that the decision maker measures uncertain rewards by their expected
value:

> SequentialDecisionProblems.CoreTheory.meas = expectedValue -- worst -- expectedValue
> SequentialDecisionProblems.FullTheory.measMon = monotoneExpectedValue -- monotoneWorst -- monotoneExpectedValue

Further on, we have to implement the notions of viability and
reachability. We start by positing that all states are viable for any
number of steps:

> -- Viable : (n : Nat) -> State t -> Type
> SequentialDecisionProblems.CoreTheory.Viable n x = Unit

From this definition, it trivially follows that all elements of an
arbitrary list of states are viable for an arbitrary number of steps:

> viableLemma : {t, n : Nat} -> (xs : List (State t)) -> All (Viable n) xs
> viableLemma  Nil      = Nil
> viableLemma {t} {n} (x :: xs) = () :: (viableLemma {t} {n} xs)

This fact and the (less trivial) result that simple probability
distributions are never empty, see |nonEmptyLemma| in
|MonadicProperties| in |SimpleProb|, allows us to show that the above
definition of |Viable| fulfills |viableSpec1|:

> -- viableSpec1 : (x : State t) -> Viable (S n) x -> GoodCtrl t x
> SequentialDecisionProblems.CoreTheory.viableSpec1 {t} {n} s v =
>   MkSigma High (ne, av) where
>     ne : SequentialDecisionProblems.CoreTheory.NotEmpty (nexts t s High)
>     ne = nonEmptyLemma (nexts t s High)
>     av : SequentialDecisionProblems.CoreTheory.All (Viable {t = S t} n) (nexts t s High)
>     av = viableLemma {t = S t} (support (nexts t s High))

> SequentialDecisionProblems.Utils.finiteViable n x = finiteUnit

> SequentialDecisionProblems.Utils.decidableViable n x = decidableUnit

For reachability, we proceed in a similar way. We say that all states
are reachable

> -- Reachable : State t' -> Type
> SequentialDecisionProblems.CoreTheory.Reachable x' = Unit

which immediately implies |reachableSpec1|:

> -- reachableSpec1 : (x : State t) -> Reachable {t' = t} x -> (y : Ctrl t x) -> All (Reachable {t' = S t}) (nexts t x y)
> SequentialDecisionProblems.CoreTheory.reachableSpec1 {t} x r y = all (nexts t x y) where
>   all : (sp : SimpleProb  (State (S t))) -> SequentialDecisionProblems.CoreTheory.All (Reachable {t' = S t}) sp
>   all sp = all' (support sp) where
>     all' : (xs : List (State (S t))) -> Data.List.Quantifiers.All (Reachable {t' = S t}) xs
>     all' Nil = Nil
>     all' (x :: xs) = () :: (all' xs)

and decidability of |Reachable|:

> SequentialDecisionProblems.TabBackwardsInduction.decidableReachable x = decidableUnit

Finally, we have to show that controls are finite

> -- finiteCtrl : {t : Nat} -> (x : State t) -> Finite (Ctrl t x)
> SequentialDecisionProblems.Utils.finiteCtrl _ = finiteLowHigh

and, in order to use the fast, tail-recursive tabulated version of
backwards induction, that states are finite:

> SequentialDecisionProblems.TabBackwardsInduction.finiteState t =
>   finiteTuple4 finiteFin finiteLowHigh finiteAvailableUnavailable finiteGoodBad


* Optimal policies, optimal decisions, ...

We can now apply the results of our |CoreTheory| and of the |FullTheory|
to compute verified optimal policies, possible state-control sequences,
etc. To this end, we need to be able to show the outcome of the decision
process. This means implemeting functions to print states and controls:

> -- showState : {t : Nat} -> State t -> String
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

> -- showControl : {t : Nat} -> {x : State t} -> Ctrl t x -> String
> SequentialDecisionProblems.Utils.showCtrl {t} {x}  Low = "L"
> SequentialDecisionProblems.Utils.showCtrl {t} {x} High = "H"

> -- ad-hoc trajectories computation
> adHocPossibleStateCtrlSeqs : {t, n : Nat} -> 
>                              (ps : PolicySeq t n) ->
>                              (x : State t) -> 
>                              SimpleProb (StateCtrlSeq t n)
> adHocPossibleStateCtrlSeqs {t} {n = Z}         Nil  x =  
>   FastSimpleProb.MonadicOperations.ret (Nil x)
> adHocPossibleStateCtrlSeqs {t} {n = S m} (p :: ps') x =
> {-  
>   FastSimpleProb.MonadicOperations.fmap ((MkSigma x y) ::) (FastSimpleProb.MonadicOperations.naivebind mx' f) where
>     y   :  Ctrl t x
>     y   =  ctrl (p x () ())
>     mx' :  SimpleProb (State (S t))
>     mx' =  nexts t x y
>     f   :  State (S t) -> M (StateCtrlSeq (S t) m)
>     f   =  adHocPossibleStateCtrlSeqs {n = m} ps'
> ---}
> --{-
>   let y   =  ctrl (p x () ()) in
>   let mx' =  nexts t x y in
>   let f   =  adHocPossibleStateCtrlSeqs {n = m} ps' in
>   FastSimpleProb.MonadicOperations.fmap ((MkSigma x y) ::) (FastSimpleProb.MonadicOperations.naivebind mx' f)
> ---}


> constHigh : (t : Nat) -> (n : Nat) -> PolicySeq t n
> constHigh t  Z    = Nil
> constHigh t (S n) = p :: (constHigh (S t) n) where
>   p : Policy t (S n)
>   p x r v = MkSigma High (ne, av) where
>     ne : SequentialDecisionProblems.CoreTheory.NotEmpty (nexts t x High)
>     ne = nonEmptyLemma (nexts t x High)
>     av : SequentialDecisionProblems.CoreTheory.All (Viable {t = S t} n) (nexts t x High)
>     av = viableLemma {t = S t} (support (nexts t x High))


> ||| Constant low policy sequences
> constLow : (t : Nat) -> (n : Nat) -> PolicySeq t n
> constLow t  Z    = Nil
> constLow t (S n) = p :: (constLow (S t) n) where
>   p : Policy t (S n)
>   p x r v = MkSigma Low (ne, av) where
>     ne : SequentialDecisionProblems.CoreTheory.NotEmpty (nexts t x Low)
>     ne = nonEmptyLemma (nexts t x Low)
>     av : SequentialDecisionProblems.CoreTheory.All (Viable {t = S t} n) (nexts t x Low)
>     av = viableLemma {t = S t} (support (nexts t x Low))

> 
> using implementation ShowNonNegDouble
>   
>   computation : { [STDIO] } Eff ()
>   computation =
>     do putStr ("enter number of steps:\n")
>        nSteps <- getNat
>        putStrLn "nSteps (number of decision steps):"
>        putStrLn ("  " ++ show nSteps)
>        
>        putStrLn "crE (crit. cumulated emissions threshold):"
>        putStrLn ("  " ++ show crE)
>        putStrLn "crN (crit. number of decision steps):" 
>        putStrLn ("  " ++ show crN)
>        
>        putStrLn "pS1 (prob. of staying in a good world, cumulated emissions below crE):"
>        putStrLn ("  " ++ show pS1)
>        putStrLn "pS2 (prob. of staying in a good world, cumulated emissions above crE):"
>        putStrLn ("  " ++ show pS2)
>        
>        putStrLn "pA1 (prob. of eff. tech. becoming available, number of steps below crN):" 
>        putStrLn ("  " ++ show pA1)
>        putStrLn "pA2 (prob. of eff. tech. becoming available, number of steps above crN):"
>        putStrLn ("  " ++ show pA2)
>        
>        putStrLn "pLL (prob. of low emission policies, emissions low, low selected):"
>        putStrLn ("  " ++ show pLL)
>        putStrLn "pLH (prob. of low emission policies, emissions high, low selected):"
>        putStrLn ("  " ++ show pLH)
>        putStrLn "pHL (prob. of high emission policies, emissions low, high selected):"
>        putStrLn ("  " ++ show pHL)
>        putStrLn "pHH (prob. of high emission policies, emissions high, high selected):"
>        putStrLn ("  " ++ show pHH) 
>        
>        putStrLn "badOverGood (step benefits ratio: bad over good world):"
>        putStrLn ("  " ++ show badOverGood)
>        putStrLn "lowOverGoodUnavailable (benefits ratio: low emissions over step, good world, eff. tech. unavailable):"
>        putStrLn ("  " ++ show lowOverGoodUnavailable) 
>        putStrLn "lowOverGoodAvailable (benefits ratio: low emissions over step, good world, eff. tech. available):"
>        putStrLn ("  " ++ show lowOverGoodAvailable)
>        putStrLn "highOverGood (benefits ratio: High emissions over step, good world):"
>        putStrLn ("  " ++ show highOverGood) 
>                  
>        putStrLn "computing constHigh policies ..."
>        constHigh_ps <- pure (constHigh Z nSteps)
>
>        putStrLn "computing constHigh state-control sequences ..."
>        constHigh_mxys <- pure (adHocPossibleStateCtrlSeqs constHigh_ps (FZ, High, Unavailable, Good))
>        putStrLn "pairing constHigh state-control sequences with their values ..."
>        constHigh_mxysv <- pure (possibleStateCtrlSeqsRewards' constHigh_mxys)
>        -- putStrLn "constHigh state-control sequences and their values:"
>        -- putStrLn (showlong constHigh_mxysv)  
>        
>        putStrLn "computing (naively) the number of constHigh state-control sequences ..."
>        constHigh_n <- pure (length (toList constHigh_mxysv))
>        putStrLn "number of constHigh state-control sequences:"
>        putStrLn ("  " ++ show constHigh_n)
>                    
>        putStrLn "computing (naively) the most probable constHigh state-control sequence ..."
>        constHigh_xysv <- pure (naiveMostProbableProb constHigh_mxysv)
>        putStrLn "most probable constHigh state-control sequence and its probability:"
>        putStrLn ("  " ++ show constHigh_xysv)            
>                    
>        putStrLn "sorting (naively) the constHigh state-control sequence ..."
>        constHigh_xysvs <- pure (naiveSortToList constHigh_mxysv)
>        putStrLn "most probable constHigh state-control sequences (first 3) and their probabilities:"
>        putStrLn (showlong (take 3 constHigh_xysvs))
>                        
>        putStrLn "measure of constHigh rewards:"
>        putStrLn ("  " ++ show (meas (SequentialDecisionProblems.CoreTheory.fmap snd constHigh_mxysv)))            
>
>        putStrLn "computing constLow policies ..."
>        constLow_ps <- pure (constLow Z nSteps)
>
>        putStrLn "computing constLow state-control sequences ..."
>        constLow_mxys <- pure (adHocPossibleStateCtrlSeqs constLow_ps (FZ, High, Unavailable, Good))
>        putStrLn "pairing constLow state-control sequences with their values ..."
>        constLow_mxysv <- pure (possibleStateCtrlSeqsRewards' constLow_mxys)
>        
>        putStrLn "computing (naively) the number of constLow state-control sequences ..."
>        constLow_n <- pure (length (toList constLow_mxysv))
>        putStrLn "number of constLow state-control sequences:"
>        putStrLn ("  " ++ show constLow_n)
>                    
>        putStrLn "computing (naively) the most probable constLow state-control sequence ..."
>        constLow_xysv <- pure (naiveMostProbableProb constLow_mxysv)
>        putStrLn "most probable constLow state-control sequence and its probability:"
>        putStrLn ("  " ++ show constLow_xysv)            
>                    
>        putStrLn "sorting (naively) the constLow state-control sequence ..."
>        constLow_xysvs <- pure (naiveSortToList constLow_mxysv)
>        putStrLn "most probable constLow state-control sequences (first 3) and their probabilities:"
>        putStrLn (showlong (take 3 constLow_xysvs))
>                        
>        putStrLn "measure of constLow rewards:"
>        putStrLn ("  " ++ show (meas (SequentialDecisionProblems.CoreTheory.fmap snd constLow_mxysv)))            
>                    
>        putStrLn "computing optimal policies ..."
>        ps <- pure (tabTailRecursiveBackwardsInduction Z nSteps)
>              
>        putStrLn "computing possible state-control sequences ..."
>        mxys <- pure (adHocPossibleStateCtrlSeqs ps (FZ, High, Unavailable, Good))
>        putStrLn "pairing possible state-control sequences with their values ..."
>        mxysv <- pure (possibleStateCtrlSeqsRewards' mxys)
>        -- putStrLn "possible state-control sequences and their values:"
>        -- putStrLn (showlong mxysv)  
>        
>        putStrLn "computing (naively) the number of possible state-control sequences ..."
>        n <- pure (length (toList mxysv))
>        putStrLn "number of possible state-control sequences:"
>        putStrLn ("  " ++ show n)
>        
>        putStrLn "computing (naively) the most probable state-control sequence ..."
>        xysv <- pure (naiveMostProbableProb mxysv)
>        putStrLn "most probable state-control sequence and its probability:"
>        putStrLn ("  " ++ show xysv)
>                        
>        putStrLn "sorting (naively) the possible state-control sequence ..."
>        xysvs <- pure (naiveSortToList mxysv)
>        putStrLn "most probable state-control sequences (first 3) and their probabilities:"
>        putStrLn (showlong (take 3 xysvs))
>                        
>        putStrLn "measure of possible rewards:"
>        putStrLn ("  " ++ show (meas (SequentialDecisionProblems.CoreTheory.fmap snd mxysv)))
   
>        putStrLn "done!"


> main : IO ()
> main = run computation


> {-

> ---}


-- Local Variables:
-- idris-packages: ("effects")
-- End:
