> module SequentialDecisionProblems.applications.Main

> import Data.Vect
> -- import Data.Fin
> -- import Data.List
> -- import Data.List.Quantifiers
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

> import BoundedNat.BoundedNat
> -- import FastSimpleProb.SimpleProb
> -- import FastSimpleProb.BasicOperations
> -- import FastSimpleProb.BasicProperties
> -- import FastSimpleProb.MonadicOperations
> -- import FastSimpleProb.MonadicProperties
> -- import FastSimpleProb.Measures
> -- import FastSimpleProb.MeasuresProperties
> -- import FastSimpleProb.Operations
> -- import Sigma.Sigma
> import Double.Predicates
> -- import Double.Postulates
> -- import Double.Operations
> -- import Double.Properties
> import NonNegDouble.NonNegDouble
> -- import NonNegDouble.Constants
> import NonNegDouble.BasicOperations
> import NonNegDouble.Operations
> import NonNegDouble.Properties
> import NonNegDouble.Predicates
> import NonNegDouble.LTEProperties
> -- import Finite.Predicates
> -- import Finite.Operations
> -- import Finite.Properties
> -- import Decidable.Predicates
> -- import Decidable.Properties
> -- import LocalEffect.Exception
> -- import LocalEffect.StdIO
> -- import Fin.Operations
> -- import List.Operations
> -- import Unit.Properties

> -- %default total
> %auto_implicits off

> -- %logging 5


* States

> data Tag = V | X | O

> Board : Type
> Board = Vect 9 Tag

> validBoard : Nat -> Board -> Bool

> data ValidBoard : Nat -> Type where
>   MkValidBoard : (t : Nat) -> (b : Board) -> validBoard t b = True -> ValidBoard t

> SequentialDecisionProblems.CoreTheory.State = ValidBoard


* Controls

> Move : Type
> Move = Maybe (LTB 9) -- Nothing is for the case the game is over before 5 rounds

> validMove : (t : Nat) -> ValidBoard t -> Move -> Bool

> data ValidMove : (t : Nat) -> ValidBoard t -> Type where
>   MkValidMove : (t : Nat) -> (b : ValidBoard t) -> (m : Move) -> validMove t b m = True -> ValidMove t b

> SequentialDecisionProblems.CoreTheory.Ctrl = ValidMove


* Transition function

> possible : (t : Nat) -> (b : ValidBoard t) -> (m : ValidMove t b) -> List (ValidBoard (S t))

> SequentialDecisionProblems.CoreTheory.nexts t x y = possible t x y


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

> won  : (t : Nat) -> (b : ValidBoard t) -> Bool
> lost : (t : Nat) -> (b : ValidBoard t) -> Bool

> SequentialDecisionProblems.CoreTheory.reward t x y x' =
>   if won (S t) x'
>   then cast 2.0
>   else if lost (S t) x'
>        then cast 0.0
>        else cast 1.0

> {-
 
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
>   let y   = ctrl (p x () ()) in
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


> computation : { [STDIO] } Eff ()
> computation =
>   do putStr ("enter number of steps:\n")
>      nSteps <- getNat
>      putStrLn "nSteps (number of decision steps):"
>      putStrLn ("  " ++ show nSteps)
>      
>      putStrLn "crE (crit. cumulated emissions threshold):"
>      putStrLn ("  " ++ show crE)
>      putStrLn "crN (crit. number of decision steps):" 
>      putStrLn ("  " ++ show crN)
>      
>      putStrLn "pS1 (prob. of staying in a good world, cumulated emissions below crE):"
>      putStrLn ("  " ++ show pS1)
>      putStrLn "pS2 (prob. of staying in a good world, cumulated emissions above crE):"
>      putStrLn ("  " ++ show pS2)
>      
>      putStrLn "pA1 (prob. of eff. tech. becoming available, number of steps below crN):" 
>      putStrLn ("  " ++ show pA1)
>      putStrLn "pA2 (prob. of eff. tech. becoming available, number of steps above crN):"
>      putStrLn ("  " ++ show pA2)
>      
>      putStrLn "pLL (prob. of low emission policies, emissions low, low selected):"
>      putStrLn ("  " ++ show pLL)
>      putStrLn "pLH (prob. of low emission policies, emissions high, low selected):"
>      putStrLn ("  " ++ show pLH)
>      putStrLn "pHL (prob. of high emission policies, emissions low, high selected):"
>      putStrLn ("  " ++ show pHL)
>      putStrLn "pHH (prob. of high emission policies, emissions high, high selected):"
>      putStrLn ("  " ++ show pHH) 
>      
>      putStrLn "badOverGood (step benefits ratio: bad over good world):"
>      putStrLn ("  " ++ show badOverGood)
>      putStrLn "lowOverGoodUnavailable (benefits ratio: low emissions over step, good world, eff. tech. unavailable):"
>      putStrLn ("  " ++ show lowOverGoodUnavailable) 
>      putStrLn "lowOverGoodAvailable (benefits ratio: low emissions over step, good world, eff. tech. available):"
>      putStrLn ("  " ++ show lowOverGoodAvailable)
>      putStrLn "highOverGood (benefits ratio: High emissions over step, good world):"
>      putStrLn ("  " ++ show highOverGood) 
>                
>      putStrLn "computing constHigh policies ..."
>      constHigh_ps <- pure (constHigh Z nSteps)
>
>      putStrLn "computing constHigh state-control sequences ..."
>      constHigh_mxys <- pure (adHocPossibleStateCtrlSeqs constHigh_ps (FZ, High, Unavailable, Good))
>      putStrLn "pairing constHigh state-control sequences with their values ..."
>      constHigh_mxysv <- pure (possibleStateCtrlSeqsRewards' constHigh_mxys)
>      -- putStrLn "constHigh state-control sequences and their values:"
>      -- putStrLn (showlong constHigh_mxysv)  
>      
>      putStrLn "computing (naively) the number of constHigh state-control sequences ..."
>      constHigh_n <- pure (length (toList constHigh_mxysv))
>      putStrLn "number of constHigh state-control sequences:"
>      putStrLn ("  " ++ show constHigh_n)
>                  
>      putStrLn "computing (naively) the most probable constHigh state-control sequence ..."
>      constHigh_xysv <- pure (naiveMostProbableProb constHigh_mxysv)
>      putStrLn "most probable constHigh state-control sequence and its probability:"
>      putStrLn ("  " ++ show constHigh_xysv)            
>                  
>      putStrLn "sorting (naively) the constHigh state-control sequence ..."
>      constHigh_xysvs <- pure (naiveSortToList constHigh_mxysv)
>      putStrLn "most probable constHigh state-control sequences (first 3) and their probabilities:"
>      putStrLn (showlong (take 3 constHigh_xysvs))
>                      
>      putStrLn "measure of constHigh rewards:"
>      putStrLn ("  " ++ show (meas (SequentialDecisionProblems.CoreTheory.fmap snd constHigh_mxysv)))            
>
>      putStrLn "computing constLow policies ..."
>      constLow_ps <- pure (constLow Z nSteps)
>
>      putStrLn "computing constLow state-control sequences ..."
>      constLow_mxys <- pure (adHocPossibleStateCtrlSeqs constLow_ps (FZ, High, Unavailable, Good))
>      putStrLn "pairing constLow state-control sequences with their values ..."
>      constLow_mxysv <- pure (possibleStateCtrlSeqsRewards' constLow_mxys)
>      
>      putStrLn "computing (naively) the number of constLow state-control sequences ..."
>      constLow_n <- pure (length (toList constLow_mxysv))
>      putStrLn "number of constLow state-control sequences:"
>      putStrLn ("  " ++ show constLow_n)
>                  
>      putStrLn "computing (naively) the most probable constLow state-control sequence ..."
>      constLow_xysv <- pure (naiveMostProbableProb constLow_mxysv)
>      putStrLn "most probable constLow state-control sequence and its probability:"
>      putStrLn ("  " ++ show constLow_xysv)            
>                  
>      putStrLn "sorting (naively) the constLow state-control sequence ..."
>      constLow_xysvs <- pure (naiveSortToList constLow_mxysv)
>      putStrLn "most probable constLow state-control sequences (first 3) and their probabilities:"
>      putStrLn (showlong (take 3 constLow_xysvs))
>                      
>      putStrLn "measure of constLow rewards:"
>      putStrLn ("  " ++ show (meas (SequentialDecisionProblems.CoreTheory.fmap snd constLow_mxysv)))            
>                  
>      putStrLn "computing optimal policies ..."
>      ps <- pure (tabTailRecursiveBackwardsInduction Z nSteps)
>            
>      putStrLn "computing possible state-control sequences ..."
>      mxys <- pure (adHocPossibleStateCtrlSeqs ps (FZ, High, Unavailable, Good))
>      putStrLn "pairing possible state-control sequences with their values ..."
>      mxysv <- pure (possibleStateCtrlSeqsRewards' mxys)
>      -- putStrLn "possible state-control sequences and their values:"
>      -- putStrLn (showlong mxysv)  
>      
>      putStrLn "computing (naively) the number of possible state-control sequences ..."
>      n <- pure (length (toList mxysv))
>      putStrLn "number of possible state-control sequences:"
>      putStrLn ("  " ++ show n)
>      
>      putStrLn "computing (naively) the most probable state-control sequence ..."
>      xysv <- pure (naiveMostProbableProb mxysv)
>      putStrLn "most probable state-control sequence and its probability:"
>      putStrLn ("  " ++ show xysv)
>                      
>      putStrLn "sorting (naively) the possible state-control sequence ..."
>      xysvs <- pure (naiveSortToList mxysv)
>      putStrLn "most probable state-control sequences (first 3) and their probabilities:"
>      putStrLn (showlong (take 3 xysvs))
>                      
>      putStrLn "measure of possible rewards:"
>      putStrLn ("  " ++ show (meas (SequentialDecisionProblems.CoreTheory.fmap snd mxysv)))
   
>      putStrLn "done!"


> main : IO ()
> main = run computation

> ---}


-- Local Variables:
-- idris-packages: ("effects")
-- End:
