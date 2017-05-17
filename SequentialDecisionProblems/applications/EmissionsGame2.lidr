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

> SequentialDecisionProblems.CoreTheory.State t 
> = (Fin (S t), LowHigh, AvailableUnavailable, GoodBad)

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
> crE = 0.0

> -- The critical number of decision steps
> crN : Nat
> crN = 8

> -- The probability of staying in a good world when the cumulated
> -- emissions are below the critical threshold |crE|
> pS1  :  NonNegDouble
> pS1  =  cast 0.9

> -- The probability of staying in a good world when the cumulated
> -- emissions are above the critical threshold |crE|
> pS2  :  NonNegDouble
> pS2  =  cast 0.1

> -- Sanity check
> pS2LTEpS1 : pS2 `NonNegDouble.Predicates.LTE` pS1
> pS2LTEpS1 = MkLTE Oh

> -- The probability of effective technologies for reducing GHG
> -- emissions becoming available when the number of decision steps is
> -- below |crN|
> pA1  :  NonNegDouble
> pA1  =  cast 0.1

> -- The probability of effective technologies for reducing GHG
> -- emissions becoming available when the number of decision steps is
> -- above |crN|
> pA2  :  NonNegDouble
> pA2  =  cast 0.9

> -- Sanity check
> pA1LTEpA2 : pA1 `NonNegDouble.Predicates.LTE` pA2
> pA1LTEpA2 = MkLTE Oh

> -- The probability being able to implement low emission policies when
> -- the current emissions are low and low emissions are selected
> pLL  :  NonNegDouble
> pLL  =  cast 0.9

> -- The probability being able to implement low emission policies when
> -- the current emissions are high and low emissions are selected
> pLH  :  NonNegDouble
> pLH  =  cast 0.7

> -- Sanity check
> pLHLTEpLL : pLH `NonNegDouble.Predicates.LTE` pLL
> pLHLTEpLL = MkLTE Oh

> -- The probability being able to implement high emission policies when
> -- the current emissions are low and high emissions are selected
> pHL  :  NonNegDouble
> pHL  =  cast 0.7

> -- The probability being able to implement high emission policies when
> -- the current emissions are high and high emissions are selected
> pHH  :  NonNegDouble
> pHH  =  cast 0.9

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
> -- The transition function: high emissions, unavailable GHG technologies, bad world
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
> -- The transition function: high emissions, available GHG technologies
>
> -- The transition function: high emissions, available GHG technologies, good world
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
> -- The transition function: high emissions, available GHG technologies, bad world
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
> -- The transition function: low emissions
>
> -- The transition function: low emissions, unavailable GHG technologies
>
> -- The transition function: low emissions, unavailable GHG technologies, good world
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
> -- The transition function: low emissions, unavailable GHG technologies, bad world
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
> -- The transition function: low emissions, available GHG technologies
>
> -- The transition function: low emissions, available GHG technologies, good world
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
> -- The transition function: low emissions, available GHG technologies, bad world
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

The idea is that being in a good world yields one unit of benefits per
step and being in a bad world yield less benefits:

> -- Ratio of the benefits in a bad world and the benefits in a good world
> badOverGood : NonNegDouble
> badOverGood = cast 0.5

> -- Sanity check
> badOverGoodLTEone : badOverGood `NonNegDouble.Predicates.LTE` one
> badOverGoodLTEone = MkLTE Oh

Emitting GHGs also brings benefits. These are a fraction of the step
benefits in a good world and low emissions bring less benefits than high
emissions:

> -- Ratio between low emissions and step benefits in good world, when
> -- effective technologies for reducing GHG emissions are unavailable
> lowOverGoodUnavailable : NonNegDouble
> lowOverGoodUnavailable = cast 0.1

> -- Ratio between low emissions and step benefits in good world, when
> -- effective technologies for reducing GHG emissions are available
> lowOverGoodAvailable : NonNegDouble
> lowOverGoodAvailable = cast 0.2

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

To be able to apply the verified, generic backwards induction algorithm
of |CoreTheory| to compute optimal policies for our problem, we have to
explain how the decision maker accounts for uncertainties on rewards
induced by uncertainties in the transition function. We first assume
that the decision maker measures uncertain rewards by their expected
value:

> SequentialDecisionProblems.CoreTheory.meas = expectedValue
> SequentialDecisionProblems.FullTheory.measMon = monotoneExpectedValue

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
>   MkSigma Low (ne, av) where
>     ne : SequentialDecisionProblems.CoreTheory.NotEmpty (nexts t s Low)
>     ne = nonEmptyLemma (nexts t s Low)
>     av : SequentialDecisionProblems.CoreTheory.All (Viable {t = S t} n) (nexts t s Low)
>     av = viableLemma {t = S t} (support (nexts t s Low))

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

> computation : { [STDIO] } Eff ()
> computation =
>   do putStr ("enter number of steps:\n")
>      nSteps <- getNat
>      case (decidableViable {t = Z} nSteps (FZ, High, Unavailable, Good)) of
>        (Yes v) => do putStrLn ("computing optimal policies ...")
>                      -- ps   <- pure (backwardsInduction Z nSteps)
>                      ps   <- pure (tabTailRecursiveBackwardsInduction Z nSteps)
>                      putStrLn ("computing optimal controls ...")
>                      mxys <- pure (possibleStateCtrlSeqs (FZ, High, Unavailable, Good) () v ps)
>                      putStrLn "possible state-control sequences:"
>                      putStr "  "
>                      putStrLn (showlong mxys)
>                      -- mvs <- pure (possibleRewards' mxys)
>                      -- putStrLn "possible rewards:"
>                      -- putStr "  "
>                      -- putStrLn (show mvs)
>                      putStrLn ("done!")
>        (No _)  => putStrLn ("initial state non viable for " ++ cast {from = Int} (cast nSteps) ++ " steps")

> main : IO ()
> main = run computation


> {-

> ---}


-- Local Variables:
-- idris-packages: ("effects")
-- End:
