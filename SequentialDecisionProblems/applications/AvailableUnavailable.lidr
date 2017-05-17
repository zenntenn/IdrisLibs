> module SequentialDecisionProblems.applications.AvailableUnavailable

> import Data.Fin
> import Control.Isomorphism

> import Finite.Predicates
> import Finite.Operations
> import Finite.Properties
> import Sigma.Sigma

> %default total
> %auto_implicits off
> %access public export


* Available / Unavailable emissions:

> data AvailableUnavailable = Available | Unavailable 


* |AvailableUnavailable| is finite and non-empty:

> to : AvailableUnavailable -> Fin 2
> to Available  =    FZ
> to Unavailable = FS FZ

> from : Fin 2 -> AvailableUnavailable
> from             FZ   = Available
> from         (FS FZ)  = Unavailable
> from     (FS (FS  k)) = absurd k

> toFrom : (k : Fin 2) -> to (from k) = k
> toFrom             FZ   = Refl
> toFrom         (FS FZ)  = Refl
> toFrom     (FS (FS  k)) = absurd k

> fromTo : (a : AvailableUnavailable) -> from (to a) = a
> fromTo Available  = Refl
> fromTo Unavailable = Refl

> ||| 
> finiteAvailableUnavailable : Finite AvailableUnavailable
> finiteAvailableUnavailable = MkSigma 2 (MkIso to from toFrom fromTo)

> |||
> cardNotZAvailableUnavailable : CardNotZ finiteAvailableUnavailable
> cardNotZAvailableUnavailable = cardNotZLemma finiteAvailableUnavailable Available


> {-

> ---}


 
