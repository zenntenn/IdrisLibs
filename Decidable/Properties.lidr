> module Decidable.Properties


> import Decidable.Predicates


> %default total

> %access public export


> ||| If |P| is decidable, |Not P| is decidable
> decNot : {P : Type} -> Dec P -> Dec (Not P)
> decNot {P} (Yes prf) = No contra where
>   contra : Not P -> Void
>   contra np = np prf
> decNot {P} (No contra) = Yes contra
> %freeze decNot -- frozen


> ||| If |P| and |Q| are decidable, |(P , Q)| is decidable
> decPair : {P, Q : Type} -> Dec P -> Dec Q -> Dec (P , Q)
> decPair (Yes p) (Yes q) = Yes (p , q)
> decPair (Yes p) (No nq) = No (\ pq => nq (snd pq))
> decPair (No np) (Yes q) = No (\ pq => np (fst pq))
> decPair (No np) (No nq) = No (\ pq => np (fst pq))
> %freeze decPair -- frozen


> ||| If |P| and |Q| are decidable, |Either P Q| is decidable
> decEither : {P, Q : Type} -> Dec P -> Dec Q -> Dec (Either P Q)
> decEither (Yes p) _       = Yes (Left p)
> decEither (No np) (Yes q) = Yes (Right q)
> decEither {P} {Q} (No np) (No nq) = No contra where
>   contra : Either P Q -> Void
>   contra (Left  p) = np p
>   contra (Right q) = nq q
> %freeze decEither -- frozen
