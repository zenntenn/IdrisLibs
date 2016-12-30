> module Void.Properties


> import Data.Fin
> import Control.Isomorphism

> import Finite.Predicates
> import Sigma.Sigma


> %default total

> %access public export


> ||| Mapping |Void|s to |Fin|s
> toFin : Void -> Fin Z
> toFin = void
> %freeze toFin


> ||| Mapping |Fin Z|s to |Void|s
> fromFin : Fin Z -> Void
> fromFin k = absurd k
> %freeze fromFin 


> ||| |toFin| is the left-inverse of |fromFin|
> toFinFromFinLemma : (k : Fin Z) -> toFin (fromFin k) = k
> toFinFromFinLemma k = absurd k
> %freeze toFinFromFinLemma


> ||| |fromFin| is the left-inverse of |toFin|
> fromFinToFinLemma : (e : Void) -> fromFin (toFin e) = e
> fromFinToFinLemma e = void e
> %freeze fromFinToFinLemma


> ||| Void is finite
> finiteVoid : Finite Void
> finiteVoid = MkSigma Z iso where
>   iso : Iso Void (Fin Z)
>   iso = MkIso toFin fromFin toFinFromFinLemma fromFinToFinLemma


> ||| Void is decidable
> decidableVoid : Dec Void
> decidableVoid = No void


> {-

> ---}
