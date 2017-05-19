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
> import SequentialDecisionProblems.NonDeterministicDefaults
> import SequentialDecisionProblems.CoreTheoryOptDefaults
> import SequentialDecisionProblems.FullTheoryOptDefaults
> import SequentialDecisionProblems.TabBackwardsInductionOptDefaults

> import SequentialDecisionProblems.applications.LowHigh
> import SequentialDecisionProblems.applications.AvailableUnavailable
> import SequentialDecisionProblems.applications.GoodBad

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
> import NonNegDouble.Measures
> import NonNegDouble.MeasureProperties
> import Finite.Predicates
> import Finite.Operations
> import Finite.Properties
> import Decidable.Predicates
> import Decidable.Properties
> import LocalEffect.Exception
> import LocalEffect.StdIO
> import Fin.Operations
> import List.Operations
> import List.Properties
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

> -- The critical cumulated emissions threshold
> crE : Double
> crE = 0.0

> -- The critical number of decision steps
> crN : Nat
> crN = 8

> -- The transition function:
>
> -- The transition function: high emissions
>
> -- The transition function: high emissions, unavailable GHG technologies
>
> -- The transition function: high emissions, unavailable GHG technologies, good world
> SequentialDecisionProblems.CoreTheory.nexts t (e, High, Unavailable, Good) Low =
>   let ttres : List (State (S t)) 
>             = [(weaken e, Low,  Unavailable, Good),
>                (    FS e, High, Unavailable, Good),
>                (weaken e, Low,    Available, Good),
>                (    FS e, High,   Available, Good),
>                (weaken e, Low,  Unavailable,  Bad),
>                (    FS e, High, Unavailable,  Bad),
>                (weaken e, Low,    Available,  Bad),
>                (    FS e, High,   Available,  Bad)] in
>   let tfres : List (State (S t)) 
>             = [(weaken e, Low,  Unavailable, Good),
>                (    FS e, High, Unavailable, Good),
>                (weaken e, Low,    Available, Good),
>                (    FS e, High,   Available, Good),
>                (weaken e, Low,  Unavailable,  Bad),
>                (    FS e, High, Unavailable,  Bad),
>                (weaken e, Low,    Available,  Bad),
>                (    FS e, High,   Available,  Bad)] in
>   let ftres : List (State (S t))  
>             = [(weaken e, Low,  Unavailable, Good),
>                (    FS e, High, Unavailable, Good),
>                (weaken e, Low,    Available, Good),
>                (    FS e, High,   Available, Good),
>                (weaken e, Low,  Unavailable,  Bad),
>                (    FS e, High, Unavailable,  Bad),
>                (weaken e, Low,    Available,  Bad),
>                (    FS e, High,   Available,  Bad)] in
>   let ffres : List (State (S t)) 
>             = [(weaken e, Low,  Unavailable, Good),
>                (    FS e, High, Unavailable, Good),
>                (weaken e, Low,    Available, Good),
>                (    FS e, High,   Available, Good),
>                (weaken e, Low,  Unavailable,  Bad),
>                (    FS e, High, Unavailable,  Bad),
>                (weaken e, Low,    Available,  Bad),
>                (    FS e, High,   Available,  Bad)] in
>   case (t <= crN) of
>     True  => case (fromFin e <= crE) of
>                True  => ttres
>                False => tfres
>     False => case (fromFin e <= crE) of
>                True  => ftres
>                False => ffres
> SequentialDecisionProblems.CoreTheory.nexts t (e, High, Unavailable, Good) High =
>   let ttres : List (State (S t)) 
>             = [(weaken e, Low,  Unavailable, Good),
>                (    FS e, High, Unavailable, Good),
>                (weaken e, Low,    Available, Good),
>                (    FS e, High,   Available, Good),
>                (weaken e, Low,  Unavailable,  Bad),
>                (    FS e, High, Unavailable,  Bad),
>                (weaken e, Low,    Available,  Bad),
>                (    FS e, High,   Available,  Bad)] in
>   let tfres : List (State (S t)) 
>             = [(weaken e, Low,  Unavailable, Good),
>                (    FS e, High, Unavailable, Good),
>                (weaken e, Low,    Available, Good),
>                (    FS e, High,   Available, Good),
>                (weaken e, Low,  Unavailable,  Bad),
>                (    FS e, High, Unavailable,  Bad),
>                (weaken e, Low,    Available,  Bad),
>                (    FS e, High,   Available,  Bad)] in
>   let ftres : List (State (S t)) 
>             = [(weaken e, Low,  Unavailable, Good),
>                (    FS e, High, Unavailable, Good),
>                (weaken e, Low,    Available, Good),
>                (    FS e, High,   Available, Good),
>                (weaken e, Low,  Unavailable,  Bad),
>                (    FS e, High, Unavailable,  Bad),
>                (weaken e, Low,    Available,  Bad),
>                (    FS e, High,   Available,  Bad)] in
>   let ffres : List (State (S t)) 
>             = [(weaken e, Low,  Unavailable, Good),
>                (    FS e, High, Unavailable, Good),
>                (weaken e, Low,    Available, Good),
>                (    FS e, High,   Available, Good),
>                (weaken e, Low,  Unavailable,  Bad),
>                (    FS e, High, Unavailable,  Bad),
>                (weaken e, Low,    Available,  Bad),
>                (    FS e, High,   Available,  Bad)] in
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
>   let ttres : List (State (S t)) 
>             = [(weaken e, Low,  Unavailable,  Bad),
>                (    FS e, High, Unavailable,  Bad),
>                (weaken e, Low,    Available,  Bad),
>                (    FS e, High,   Available,  Bad)] in
>   let tfres : List (State (S t)) 
>             = [(weaken e, Low,  Unavailable,  Bad),
>                (    FS e, High, Unavailable,  Bad),
>                (weaken e, Low,    Available,  Bad),
>                (    FS e, High,   Available,  Bad)] in
>   let ftres : List (State (S t)) 
>             = [(weaken e, Low,  Unavailable,  Bad),
>                (    FS e, High, Unavailable,  Bad),
>                (weaken e, Low,    Available,  Bad),
>                (    FS e, High,   Available,  Bad)] in
>   let ffres : List (State (S t)) 
>             = [(weaken e, Low,  Unavailable,  Bad),
>                (    FS e, High, Unavailable,  Bad),
>                (weaken e, Low,    Available,  Bad),
>                (    FS e, High,   Available,  Bad)] in
>   case (t <= crN) of
>     True  => case (fromFin e <= crE) of
>                True  => ttres
>                False => tfres
>     False => case (fromFin e <= crE) of
>                True  => ftres
>                False => ffres
> SequentialDecisionProblems.CoreTheory.nexts t (e, High, Unavailable, Bad) High =
>   let ttres : List (State (S t)) 
>             = [(weaken e, Low,  Unavailable,  Bad),
>                (    FS e, High, Unavailable,  Bad),
>                (weaken e, Low,    Available,  Bad),
>                (    FS e, High,   Available,  Bad)] in
>   let tfres : List (State (S t)) 
>             = [(weaken e, Low,  Unavailable,  Bad),
>                (    FS e, High, Unavailable,  Bad),
>                (weaken e, Low,    Available,  Bad),
>                (    FS e, High,   Available,  Bad)] in
>   let ftres : List (State (S t)) 
>             = [(weaken e, Low,  Unavailable,  Bad),
>                (    FS e, High, Unavailable,  Bad),
>                (weaken e, Low,    Available,  Bad),
>                (    FS e, High,   Available,  Bad)] in
>   let ffres : List (State (S t)) 
>             = [(weaken e, Low,  Unavailable,  Bad),
>                (    FS e, High, Unavailable,  Bad),
>                (weaken e, Low,    Available,  Bad),
>                (    FS e, High,   Available,  Bad)] in
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
>   let ttres : List (State (S t)) 
>             = [(weaken e, Low,    Available, Good),
>                (    FS e, High,   Available, Good),
>                (weaken e, Low,    Available,  Bad),
>                (    FS e, High,   Available,  Bad)] in
>   let tfres : List (State (S t)) 
>             = [(weaken e, Low,    Available, Good),
>                (    FS e, High,   Available, Good),
>                (weaken e, Low,    Available,  Bad),
>                (    FS e, High,   Available,  Bad)] in
>   let ftres : List (State (S t)) 
>             = [(weaken e, Low,    Available, Good),
>                (    FS e, High,   Available, Good),
>                (weaken e, Low,    Available,  Bad),
>                (    FS e, High,   Available,  Bad)] in
>   let ffres : List (State (S t)) 
>             = [(weaken e, Low,    Available, Good),
>                (    FS e, High,   Available, Good),
>                (weaken e, Low,    Available,  Bad),
>                (    FS e, High,   Available,  Bad)] in
>   case (t <= crN) of
>     True  => case (fromFin e <= crE) of
>                True  => ttres
>                False => tfres
>     False => case (fromFin e <= crE) of
>                True  => ftres
>                False => ffres
> SequentialDecisionProblems.CoreTheory.nexts t (e, High, Available, Good) High =
>   let ttres : List (State (S t)) 
>             = [(weaken e, Low,    Available, Good),
>                (    FS e, High,   Available, Good),
>                (weaken e, Low,    Available,  Bad),
>                (    FS e, High,   Available,  Bad)] in
>   let tfres : List (State (S t)) 
>             = [(weaken e, Low,    Available, Good),
>                (    FS e, High,   Available, Good),
>                (weaken e, Low,    Available,  Bad),
>                (    FS e, High,   Available,  Bad)] in
>   let ftres : List (State (S t)) 
>             = [(weaken e, Low,    Available, Good),
>                (    FS e, High,   Available, Good),
>                (weaken e, Low,    Available,  Bad),
>                (    FS e, High,   Available,  Bad)] in
>   let ffres : List (State (S t)) 
>             = [(weaken e, Low,    Available, Good),
>                (    FS e, High,   Available, Good),
>                (weaken e, Low,    Available,  Bad),
>                (    FS e, High,   Available,  Bad)] in
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
>   let ttres : List (State (S t)) 
>             = [(weaken e, Low,    Available,  Bad),
>                (    FS e, High,   Available,  Bad)] in
>   let tfres : List (State (S t)) 
>             = [(weaken e, Low,    Available,  Bad),
>                (    FS e, High,   Available,  Bad)] in
>   let ftres : List (State (S t)) 
>             = [(weaken e, Low,    Available,  Bad),
>                (    FS e, High,   Available,  Bad)] in
>   let ffres : List (State (S t)) 
>             = [(weaken e, Low,    Available,  Bad),
>                (    FS e, High,   Available,  Bad)] in
>   case (t <= crN) of
>     True  => case (fromFin e <= crE) of
>                True  => ttres
>                False => tfres
>     False => case (fromFin e <= crE) of
>                True  => ftres
>                False => ffres
> SequentialDecisionProblems.CoreTheory.nexts t (e, High, Available, Bad) High =
>   let ttres : List (State (S t)) 
>             = [(weaken e, Low,    Available,  Bad),
>                (    FS e, High,   Available,  Bad)] in
>   let tfres : List (State (S t)) 
>             = [(weaken e, Low,    Available,  Bad),
>                (    FS e, High,   Available,  Bad)] in
>   let ftres : List (State (S t)) 
>             = [(weaken e, Low,    Available,  Bad),
>                (    FS e, High,   Available,  Bad)] in
>   let ffres : List (State (S t)) 
>             = [(weaken e, Low,    Available,  Bad),
>                (    FS e, High,   Available,  Bad)] in
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
>   let ttres : List (State (S t)) 
>             = [(weaken e, Low,  Unavailable, Good),
>                (    FS e, High, Unavailable, Good),
>                (weaken e, Low,    Available, Good),
>                (    FS e, High,   Available, Good),
>                (weaken e, Low,  Unavailable,  Bad),
>                (    FS e, High, Unavailable,  Bad),
>                (weaken e, Low,    Available,  Bad),
>                (    FS e, High,   Available,  Bad)] in
>   let tfres : List (State (S t)) 
>             = [(weaken e, Low,  Unavailable, Good),
>                (    FS e, High, Unavailable, Good),
>                (weaken e, Low,    Available, Good),
>                (    FS e, High,   Available, Good),
>                (weaken e, Low,  Unavailable,  Bad),
>                (    FS e, High, Unavailable,  Bad),
>                (weaken e, Low,    Available,  Bad),
>                (    FS e, High,   Available,  Bad)] in
>   let ftres : List (State (S t)) 
>             = [(weaken e, Low,  Unavailable, Good),
>                (    FS e, High, Unavailable, Good),
>                (weaken e, Low,    Available, Good),
>                (    FS e, High,   Available, Good),
>                (weaken e, Low,  Unavailable,  Bad),
>                (    FS e, High, Unavailable,  Bad),
>                (weaken e, Low,    Available,  Bad),
>                (    FS e, High,   Available,  Bad)] in
>   let ffres : List (State (S t)) 
>             = [(weaken e, Low,  Unavailable, Good),
>                (    FS e, High, Unavailable, Good),
>                (weaken e, Low,    Available, Good),
>                (    FS e, High,   Available, Good),
>                (weaken e, Low,  Unavailable,  Bad),
>                (    FS e, High, Unavailable,  Bad),
>                (weaken e, Low,    Available,  Bad),
>                (    FS e, High,   Available,  Bad)] in
>   case (t <= crN) of
>     True  => case (fromFin e <= crE) of
>                True  => ttres
>                False => tfres
>     False => case (fromFin e <= crE) of
>                True  => ftres
>                False => ffres
> SequentialDecisionProblems.CoreTheory.nexts t (e, Low, Unavailable, Good) High =
>   let ttres : List (State (S t)) 
>             = [(weaken e, Low,  Unavailable, Good),
>                (    FS e, High, Unavailable, Good),
>                (weaken e, Low,    Available, Good),
>                (    FS e, High,   Available, Good),
>                (weaken e, Low,  Unavailable,  Bad),
>                (    FS e, High, Unavailable,  Bad),
>                (weaken e, Low,    Available,  Bad),
>                (    FS e, High,   Available,  Bad)] in
>   let tfres : List (State (S t)) 
>             = [(weaken e, Low,  Unavailable, Good),
>                (    FS e, High, Unavailable, Good),
>                (weaken e, Low,    Available, Good),
>                (    FS e, High,   Available, Good),
>                (weaken e, Low,  Unavailable,  Bad),
>                (    FS e, High, Unavailable,  Bad),
>                (weaken e, Low,    Available,  Bad),
>                (    FS e, High,   Available,  Bad)] in
>   let ftres : List (State (S t)) 
>             = [(weaken e, Low,  Unavailable, Good),
>                (    FS e, High, Unavailable, Good),
>                (weaken e, Low,    Available, Good),
>                (    FS e, High,   Available, Good),
>                (weaken e, Low,  Unavailable,  Bad),
>                (    FS e, High, Unavailable,  Bad),
>                (weaken e, Low,    Available,  Bad),
>                (    FS e, High,   Available,  Bad)] in
>   let ffres : List (State (S t)) 
>             = [(weaken e, Low,  Unavailable, Good),
>                (    FS e, High, Unavailable, Good),
>                (weaken e, Low,    Available, Good),
>                (    FS e, High,   Available, Good),
>                (weaken e, Low,  Unavailable,  Bad),
>                (    FS e, High, Unavailable,  Bad),
>                (weaken e, Low,    Available,  Bad),
>                (    FS e, High,   Available,  Bad)] in
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
>   let ttres : List (State (S t)) 
>             = [(weaken e, Low,  Unavailable,  Bad),
>                (    FS e, High, Unavailable,  Bad),
>                (weaken e, Low,    Available,  Bad),
>                (    FS e, High,   Available,  Bad)] in
>   let tfres : List (State (S t)) 
>             = [(weaken e, Low,  Unavailable,  Bad),
>                (    FS e, High, Unavailable,  Bad),
>                (weaken e, Low,    Available,  Bad),
>                (    FS e, High,   Available,  Bad)] in
>   let ftres : List (State (S t)) 
>             = [(weaken e, Low,  Unavailable,  Bad),
>                (    FS e, High, Unavailable,  Bad),
>                (weaken e, Low,    Available,  Bad),
>                (    FS e, High,   Available,  Bad)] in
>   let ffres : List (State (S t)) 
>             = [(weaken e, Low,  Unavailable,  Bad),
>                (    FS e, High, Unavailable,  Bad),
>                (weaken e, Low,    Available,  Bad),
>                (    FS e, High,   Available,  Bad)] in
>   case (t <= crN) of
>     True  => case (fromFin e <= crE) of
>                True  => ttres
>                False => tfres
>     False => case (fromFin e <= crE) of
>                True  => ftres
>                False => ffres
> SequentialDecisionProblems.CoreTheory.nexts t (e, Low, Unavailable, Bad) High =
>   let ttres : List (State (S t)) 
>             = [(weaken e, Low,  Unavailable,  Bad),
>                (    FS e, High, Unavailable,  Bad),
>                (weaken e, Low,    Available,  Bad),
>                (    FS e, High,   Available,  Bad)] in
>   let tfres : List (State (S t)) 
>             = [(weaken e, Low,  Unavailable,  Bad),
>                (    FS e, High, Unavailable,  Bad),
>                (weaken e, Low,    Available,  Bad),
>                (    FS e, High,   Available,  Bad)] in
>   let ftres : List (State (S t)) 
>             = [(weaken e, Low,  Unavailable,  Bad),
>                (    FS e, High, Unavailable,  Bad),
>                (weaken e, Low,    Available,  Bad),
>                (    FS e, High,   Available,  Bad)] in
>   let ffres : List (State (S t)) 
>             = [(weaken e, Low,  Unavailable,  Bad),
>                (    FS e, High, Unavailable,  Bad),
>                (weaken e, Low,    Available,  Bad),
>                (    FS e, High,   Available,  Bad)] in
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
>   let ttres : List (State (S t)) 
>             = [(weaken e, Low,    Available, Good),
>                (    FS e, High,   Available, Good),
>                (weaken e, Low,    Available,  Bad),
>                (    FS e, High,   Available,  Bad)] in
>   let tfres : List (State (S t)) 
>             = [(weaken e, Low,    Available, Good),
>                (    FS e, High,   Available, Good),
>                (weaken e, Low,    Available,  Bad),
>                (    FS e, High,   Available,  Bad)] in
>   let ftres : List (State (S t)) 
>             = [(weaken e, Low,    Available, Good),
>                (    FS e, High,   Available, Good),
>                (weaken e, Low,    Available,  Bad),
>                (    FS e, High,   Available,  Bad)] in
>   let ffres : List (State (S t)) 
>             = [(weaken e, Low,    Available, Good),
>                (    FS e, High,   Available, Good),
>                (weaken e, Low,    Available,  Bad),
>                (    FS e, High,   Available,  Bad)] in
>   case (t <= crN) of
>     True  => case (fromFin e <= crE) of
>                True  => ttres
>                False => tfres
>     False => case (fromFin e <= crE) of
>                True  => ftres
>                False => ffres
> SequentialDecisionProblems.CoreTheory.nexts t (e, Low, Available, Good) High =
>   let ttres : List (State (S t)) 
>             = [(weaken e, Low,    Available, Good),
>                (    FS e, High,   Available, Good),
>                (weaken e, Low,    Available,  Bad),
>                (    FS e, High,   Available,  Bad)] in
>   let tfres : List (State (S t)) 
>             = [(weaken e, Low,    Available, Good),
>                (    FS e, High,   Available, Good),
>                (weaken e, Low,    Available,  Bad),
>                (    FS e, High,   Available,  Bad)] in
>   let ftres : List (State (S t)) 
>             = [(weaken e, Low,    Available, Good),
>                (    FS e, High,   Available, Good),
>                (weaken e, Low,    Available,  Bad),
>                (    FS e, High,   Available,  Bad)] in
>   let ffres : List (State (S t)) 
>             = [(weaken e, Low,    Available, Good),
>                (    FS e, High,   Available, Good),
>                (weaken e, Low,    Available,  Bad),
>                (    FS e, High,   Available,  Bad)] in
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
>   let ttres : List (State (S t)) 
>             = [(weaken e, Low,    Available,  Bad),
>                (    FS e, High,   Available,  Bad)] in
>   let tfres : List (State (S t)) 
>             = [(weaken e, Low,    Available,  Bad),
>                (    FS e, High,   Available,  Bad)] in
>   let ftres : List (State (S t)) 
>             = [(weaken e, Low,    Available,  Bad),
>                (    FS e, High,   Available,  Bad)] in
>   let ffres : List (State (S t)) 
>             = [(weaken e, Low,    Available,  Bad),
>                (    FS e, High,   Available,  Bad)] in
>   case (t <= crN) of
>     True  => case (fromFin e <= crE) of
>                True  => ttres
>                False => tfres
>     False => case (fromFin e <= crE) of
>                True  => ftres
>                False => ffres
> SequentialDecisionProblems.CoreTheory.nexts t (e, Low, Available, Bad) High =
>   let ttres : List (State (S t)) 
>             = [(weaken e, Low,    Available,  Bad),
>                (    FS e, High,   Available,  Bad)] in
>   let tfres : List (State (S t)) 
>             = [(weaken e, Low,    Available,  Bad),
>                (    FS e, High,   Available,  Bad)] in
>   let ftres : List (State (S t)) 
>             = [(weaken e, Low,    Available,  Bad),
>                (    FS e, High,   Available,  Bad)] in
>   let ffres : List (State (S t)) 
>             = [(weaken e, Low,    Available,  Bad),
>                (    FS e, High,   Available,  Bad)] in
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

> -- Ratio of the benefits in a bad world and the benefits in a good world
> badOverGood : NonNegDouble
> badOverGood = cast 0.5

> -- Sanity check
> badOverGoodLTEone : badOverGood `NonNegDouble.Predicates.LTE` one
> badOverGoodLTEone = MkLTE Oh

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

> SequentialDecisionProblems.CoreTheory.meas = average
> SequentialDecisionProblems.FullTheory.measMon = monotoneAverage

Further on, we have to implement the notions of viability and
reachability. We start by positing that all states are viable for any
number of steps:

> -- Viable : (n : Nat) -> State t -> Type
> SequentialDecisionProblems.CoreTheory.Viable n x = Unit

From this definition, it trivially follows that all elements of an
arbitrary list of states are viable for an arbitrary number of steps:

> viableLemma : {t, n : Nat} -> (xs : List (State t)) -> SequentialDecisionProblems.CoreTheory.All (Viable n) xs
> viableLemma  Nil      = Nil
> viableLemma {t} {n} (x :: xs) = () :: (viableLemma {t} {n} xs)

This fact and the (less trivial) result that simple probability
distributions are never empty, see |nonEmptyLemma| in
|MonadicProperties| in |List|, allows us to show that the above
definition of |Viable| fulfills |viableSpec1|:

> -- viableSpec1 : (x : State t) -> Viable (S n) x -> GoodCtrl t x
> SequentialDecisionProblems.CoreTheory.viableSpec1 {t} {n} s v =
>   MkSigma Low (ne, av) where
>     ne : SequentialDecisionProblems.CoreTheory.NotEmpty (nexts t s Low)
>     ne = ?kika -- nonEmptyLemma (nexts t s Low)
>     av : SequentialDecisionProblems.CoreTheory.All (Viable {t = S t} n) (nexts t s Low)
>     av = viableLemma {t = S t} (nexts t s Low)

> SequentialDecisionProblems.Utils.finiteViable n x = finiteUnit

> SequentialDecisionProblems.Utils.decidableViable n x = decidableUnit

For reachability, we proceed in a similar way. We say that all states
are reachable

> -- Reachable : State t' -> Type
> SequentialDecisionProblems.CoreTheory.Reachable x' = Unit

which immediately implies |reachableSpec1|:

> -- reachableSpec1 : (x : State t) -> Reachable {t' = t} x -> (y : Ctrl t x) -> All (Reachable {t' = S t}) (nexts t x y)
> SequentialDecisionProblems.CoreTheory.reachableSpec1 {t} x r y = all (nexts t x y) where
>   all : (xs : List (State (S t))) -> SequentialDecisionProblems.CoreTheory.All (Reachable {t' = S t}) xs
>   all Nil = Nil
>   all (x :: xs) = () :: (all xs)

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
> adHocPossibleStateCtrlSeqs  :  {t, n : Nat} -> (x : State t) -> 
>                                (ps : PolicySeq t n) ->
>                                M (StateCtrlSeq t n)
> adHocPossibleStateCtrlSeqs {t} {n = Z}    x  Nil        =  
>   [(Nil x)]
> adHocPossibleStateCtrlSeqs {t} {n = S m}  x (p :: ps')  =
>   map ((MkSigma x y) ::) (mx' >>= f) where
>     y   :  Ctrl t x
>     y   =  ctrl (p x () ())
>     mx' :  M (State (S t))
>     mx' =  nexts t x y
>     f   :  State (S t) -> M (StateCtrlSeq (S t) m)
>     f x' = adHocPossibleStateCtrlSeqs {n = m} x' ps'

> adHocApp : {t, m, n : Nat} ->
>            StateCtrlSeq t m -> Policy (t + m) (S n) -> M (StateCtrlSeq t (S m))
> adHocApp {t} {m = Z} {n} (Nil {t} x) p = map (f . g) (nexts t x y) where
>   q : Policy t (S n)
>   q = replace {P = \ X => Policy X (S n)} (plusZeroRightNeutral t) p
>   y : Ctrl t x
>   y = ctrl (q x () ())
>   f : StateCtrlSeq (S t) Z -> StateCtrlSeq t (S Z)
>   f = ((MkSigma x y) ::)
>   g : State (S t) -> StateCtrlSeq (S t) Z
>   g x' = Nil x'
> adHocApp {t} {m = S m'} {n} (xy :: xys) p = map f (adHocApp xys q) where
>   f : StateCtrlSeq (S t) (S m') -> StateCtrlSeq t (S (S m'))
>   f = (xy ::)
>   q : Policy (S t + m') (S n)
>   q = replace {P = \ X => Policy X (S n)} (sym (plusSuccRightSucc t m')) p

> adHocExtend : {t, m, n : Nat} ->
>               M (StateCtrlSeq t m) -> PolicySeq (t + m) n -> M (StateCtrlSeq t (m + n))
> adHocExtend mxys {t} {m} {n = Z}         Nil  = 
>   replace {P = \ X => M (StateCtrlSeq t X)} (sym (plusZeroRightNeutral m)) mxys
> adHocExtend mxys {t} {m} {n = S n'} (p :: ps) = s2 where
>   s1 : M (StateCtrlSeq t (plus (S m) n'))
>   s1 = adHocExtend mxys' (replace {P = \ X => PolicySeq X n'} (plusSuccRightSucc t m) ps) where
>     mxys' : M (StateCtrlSeq t (S m))
>     mxys' = mxys >>= f where
>       f : StateCtrlSeq t m ->  M (StateCtrlSeq t (S m))
>       f xys = adHocApp xys p
>   s2 : M (StateCtrlSeq t (plus m (S n')))
>   s2 = replace {P = \ X => M (StateCtrlSeq t X)} (plusSuccRightSucc m n') s1     

> adHocPossibleStateCtrlSeqs1 : {t, n : Nat} -> (x : State t) ->
>                               (ps : PolicySeq t n) -> M (StateCtrlSeq t n)
> adHocPossibleStateCtrlSeqs1 {t} {n} x ps = s2 where
>   
>   s1 : M (StateCtrlSeq t (Z + n))
>   s1 = adHocExtend [(Nil {t} x)] (replace {P = \ X => PolicySeq X n} (sym (plusZeroRightNeutral t)) ps)
>   s2 : M (StateCtrlSeq t n)
>   s2 = replace {P = \ X => M (StateCtrlSeq t X)} (plusZeroLeftNeutral n) s1


> computation : { [STDIO] } Eff ()
> computation =
>   do putStr ("enter number of steps:\n")
>      nSteps <- getNat
>      case (decidableViable {t = Z} nSteps (FZ, High, Unavailable, Good)) of
>        (Yes v) => do putStrLn ("computing optimal policies ...")
>                      -- ps   <- pure (backwardsInduction Z nSteps)
>                      ps   <- pure (tabTailRecursiveBackwardsInduction Z nSteps)
>                      putStrLn ("computing optimal controls ...")
>                      -- mxys <- pure (possibleStateCtrlSeqs (FZ, High, Unavailable, Good) () v ps)
>                      mxys <- pure (adHocPossibleStateCtrlSeqs (FZ, High, Unavailable, Good) ps)
>                      putStrLn "possible state-control sequences:"
>                      putStr "  "
>                      putStrLn (showlong mxys)
>                      mvs <- pure (possibleRewards' mxys)
>                      putStrLn "possible rewards:"
>                      putStr "  "
>                      putStrLn (show mvs)
>                      putStrLn ("done!")
>        (No _)  => putStrLn ("initial state non viable for " ++ cast {from = Int} (cast nSteps) ++ " steps")

> main : IO ()
> main = run computation


> {-


> ---}


-- Local Variables:
-- idris-packages: ("effects")
-- End:
