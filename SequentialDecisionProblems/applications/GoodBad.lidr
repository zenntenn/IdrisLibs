> module SequentialDecisionProblems.applications.GoodBad

> import Data.Fin
> import Control.Isomorphism

> import Finite.Predicates
> import Finite.Operations
> import Finite.Properties
> import Sigma.Sigma

> %default total
> %auto_implicits off
> %access public export


* Good / Bad options:

> data GoodBad = Good | Bad 


* |GoodBad| is finite and non-empty:

> to : GoodBad -> Fin 2
> to Good   =    FZ
> to Bad = FS FZ

> from : Fin 2 -> GoodBad
> from             FZ   = Good
> from         (FS FZ)  = Bad
> from     (FS (FS  k)) = absurd k

> toFrom : (k : Fin 2) -> to (from k) = k
> toFrom             FZ   = Refl
> toFrom         (FS FZ)  = Refl
> toFrom     (FS (FS  k)) = absurd k

> fromTo : (a : GoodBad) -> from (to a) = a
> fromTo Good = Refl
> fromTo  Bad = Refl

> ||| 
> finiteGoodBad : Finite GoodBad
> finiteGoodBad = MkSigma 2 (MkIso to from toFrom fromTo)

> |||
> cardNotZGoodBad : CardNotZ finiteGoodBad
> cardNotZGoodBad = cardNotZLemma finiteGoodBad Good


* |GoodBad| is in |Eq|:

> implementation Eq GoodBad where
>   (==) Good Good = True
>   (==) Good  Bad = False
>   (==)  Bad Good = False
>   (==)  Bad  Bad = True


> {-

> ---}


 
