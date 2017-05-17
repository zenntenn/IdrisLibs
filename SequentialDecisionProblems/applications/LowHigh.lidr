> module SequentialDecisionProblems.applications.LowHigh

> import Data.Fin
> import Control.Isomorphism

> import Finite.Predicates
> import Finite.Operations
> import Finite.Properties
> import Sigma.Sigma

> %default total
> %auto_implicits off
> %access public export


* Low / High emissions:

> data LowHigh = Low | High 


* |LowHigh| is finite and non-empty:

> to : LowHigh -> Fin 2
> to Low  =    FZ
> to High = FS FZ

> from : Fin 2 -> LowHigh
> from             FZ   = Low
> from         (FS FZ)  = High
> from     (FS (FS  k)) = absurd k

> toFrom : (k : Fin 2) -> to (from k) = k
> toFrom             FZ   = Refl
> toFrom         (FS FZ)  = Refl
> toFrom     (FS (FS  k)) = absurd k

> fromTo : (a : LowHigh) -> from (to a) = a
> fromTo Low  = Refl
> fromTo High = Refl

> ||| 
> finiteLowHigh : Finite LowHigh
> finiteLowHigh = MkSigma 2 (MkIso to from toFrom fromTo)

> |||
> cardNotZLowHigh : CardNotZ finiteLowHigh
> cardNotZLowHigh = cardNotZLemma finiteLowHigh Low


> {-

> ---}


 
