> module SequentialDecisionProblems.applications.FreezeOrIncrease

> import Data.Fin
> import Control.Isomorphism

> import Finite.Predicates
> import Finite.Operations
> import Finite.Properties
> import Sigma.Sigma

> %default total
> %auto_implicits off
> %access public export


* Freeze / Increase options:

> data FreezeOrIncrease = Freeze | Increase 


* |FreezeOrIncrease| is finite and non-empty:

> to : FreezeOrIncrease -> Fin 2
> to Freeze   =    FZ
> to Increase = FS FZ

> from : Fin 2 -> FreezeOrIncrease
> from             FZ   = Freeze
> from         (FS FZ)  = Increase
> from     (FS (FS  k)) = absurd k

> toFrom : (k : Fin 2) -> to (from k) = k
> toFrom             FZ   = Refl
> toFrom         (FS FZ)  = Refl
> toFrom     (FS (FS  k)) = absurd k

> fromTo : (a : FreezeOrIncrease) -> from (to a) = a
> fromTo Freeze   = Refl
> fromTo Increase = Refl

> ||| 
> finiteFreezeOrIncrease : Finite FreezeOrIncrease
> finiteFreezeOrIncrease = MkSigma 2 (MkIso to from toFrom fromTo)

> |||
> cardNotZFreezeOrIncrease : CardNotZ finiteFreezeOrIncrease
> cardNotZFreezeOrIncrease = cardNotZLemma finiteFreezeOrIncrease Freeze


> {-

> ---}


 
