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

> import FastSimpleProb.SimpleProb
> import FastSimpleProb.BasicOperations
> import FastSimpleProb.BasicProperties
> import FastSimpleProb.MonadicOperations
> import FastSimpleProb.MonadicProperties
> import FastSimpleProb.Measures
> import FastSimpleProb.MeasuresProperties
> import FastSimpleProb.Operations
> import Sigma.Sigma
> import Sigma.Operations
> import Sigma.Properties
> import Nat.LTProperties
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
> import Unique.Predicates
> import Decidable.Predicates
> import Decidable.Properties
> import LocalEffect.Exception
> import LocalEffect.StdIO
> import Fin.Operations
> import Fraction.Fraction
> import Fraction.Normal
> import Nat.Positive
> import List.Operations
> import Unit.Properties

> -- %default total
> %auto_implicits off
> -- %logging 5

> computation : { [STDIO] } Eff ()
> computation =
>   do putStrLn "done!"

> main : IO ()
> main = run computation


> {-

> ---}


-- Local Variables:
-- idris-packages: ("effects")
-- End:
