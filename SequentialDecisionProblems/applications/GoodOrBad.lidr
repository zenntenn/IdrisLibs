> module SequentialDecisionProblems.applications.GoodOrBad

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

> data GoodOrBad = Good | Bad 


* |GoodOrBad| is finite and non-empty:

> to : GoodOrBad -> Fin 2
> to Good   =    FZ
> to Bad = FS FZ

> from : Fin 2 -> GoodOrBad
> from             FZ   = Good
> from         (FS FZ)  = Bad
> from     (FS (FS  k)) = absurd k

> toFrom : (k : Fin 2) -> to (from k) = k
> toFrom             FZ   = Refl
> toFrom         (FS FZ)  = Refl
> toFrom     (FS (FS  k)) = absurd k

> fromTo : (a : GoodOrBad) -> from (to a) = a
> fromTo Good = Refl
> fromTo  Bad = Refl

> ||| 
> finiteGoodOrBad : Finite GoodOrBad
> finiteGoodOrBad = MkSigma 2 (MkIso to from toFrom fromTo)

> |||
> cardNotZGoodOrBad : CardNotZ finiteGoodOrBad
> cardNotZGoodOrBad = cardNotZLemma finiteGoodOrBad Good


> {-

> ---}


 
