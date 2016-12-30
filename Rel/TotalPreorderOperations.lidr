> module Rel.TotalPreorderOperations

> import Rel.TotalPreorder

> %default total

> %access public export


> {-
> ||| R
> R : {A : Type} -> {R : A -> A -> Type} -> TotalPreorder R -> (A -> A -> Type)
> R (MkTotalPreorder R _ _ _) = R
> -}


> ||| reflexive
> reflexive : {A : Type} -> {R : A -> A -> Type} -> 
>             TotalPreorder R -> 
>             (x : A) -> R x x
> reflexive (MkTotalPreorder _ reflexive _ _) = reflexive


> ||| transitive
> transitive : {A : Type} -> {R : A -> A -> Type} -> 
>              TotalPreorder R ->
>              (x : A) -> (y : A) -> (z : A) -> R x y -> R y z -> R x z
> transitive (MkTotalPreorder _ _ transitive _) = transitive


> ||| totalPre
> totalPre : {A : Type} -> {R : A -> A -> Type} -> 
>            TotalPreorder R ->
>            (x : A) -> (y : A) -> Either (R x y) (R y x)
> totalPre (MkTotalPreorder _ _ _ totalPre) = totalPre


> ||| 
> extendRight : {A, B : Type} -> 
>               (A -> A -> Type) -> ((A, B) -> (A, B) -> Type)
> extendRight R = \ x => \ y => R (fst x) (fst y)


> ||| |extendRight| preserves total preorders
> extendRightLemma : {A, B : Type} -> {R : A -> A -> Type} -> 
>                    TotalPreorder R -> TotalPreorder (extendRight {A} {B} R)
> extendRightLemma {A} {B} {R} (MkTotalPreorder R reflexiveR transitiveR totalR) =
>   MkTotalPreorder S reflexiveS transitiveS totalS where
>     S           : (A, B) -> (A, B) -> Type
>     S           = extendRight R
>     reflexiveS  : (x : (A, B)) -> S x x
>     reflexiveS  = \ x => reflexiveR (fst x)
>     transitiveS : (x : (A, B)) -> (y : (A, B)) -> (z : (A, B)) -> S x y -> S y z -> S x z
>     transitiveS = \ x => \ y => \ z => \ xRy => \ yRz => transitiveR (fst x) (fst y) (fst z) xRy yRz
>     totalS      : (x : (A, B)) -> (y : (A, B)) -> Either (S x y) (S y x)
>     totalS      = \ x => \ y => totalR (fst x) (fst y)


> ||| 
> extendLeft : {A, B : Type} -> 
>              (B -> B -> Type) -> ((A, B) -> (A, B) -> Type)
> extendLeft R = \ x => \ y => R (snd x) (snd y)


> ||| |extendRight| preserves total preorders
> extendLeftLemma : {A, B : Type} -> {R : B -> B -> Type} -> 
>                   TotalPreorder R -> TotalPreorder (extendLeft {A} {B} R)
> extendLeftLemma {A} {B} {R} (MkTotalPreorder R reflexiveR transitiveR totalR) =
>   MkTotalPreorder S reflexiveS transitiveS totalS where
>     S           : (A, B) -> (A, B) -> Type
>     S           = extendLeft R
>     reflexiveS  : (x : (A, B)) -> S x x
>     reflexiveS  = \ x => reflexiveR (snd x)
>     transitiveS : (x : (A, B)) -> (y : (A, B)) -> (z : (A, B)) -> S x y -> S y z -> S x z
>     transitiveS = \ x => \ y => \ z => \ xRy => \ yRz => transitiveR (snd x) (snd y) (snd z) xRy yRz
>     totalS      : (x : (A, B)) -> (y : (A, B)) -> Either (S x y) (S y x)
>     totalS      = \ x => \ y => totalR (snd x) (snd y)


> {-

> ||| R
> R : {A : Type} -> TotalPreorder A -> (A -> A -> Type)
> R (MkTotalPreorder R _ _ _) = R


> ||| reflexive
> reflexive : {A : Type} ->
>             (tp : TotalPreorder A) ->
>             (x : A) -> (R tp) x x
> reflexive (MkTotalPreorder _ reflexive _ _) = reflexive


> ||| transitive
> transitive : {A : Type} ->
>              (tp : TotalPreorder A) ->
>              (x : A) -> (y : A) -> (z : A) -> (R tp) x y -> (R tp) y z -> (R tp) x z
> transitive (MkTotalPreorder _ _ transitive _) = transitive


> ||| totalPre
> totalPre : {A : Type} ->
>          (tp : TotalPreorder A) ->
>          (x : A) -> (y : A) -> Either ((R tp) x y) ((R tp) y x)
> totalPre (MkTotalPreorder _ _ _ totalPre) = totalPre


> ||| Total preorders on |A| induce total preorders on |(A, B)|
> fromTotalPreorder1 : {A, B : Type} -> TotalPreorder A -> TotalPreorder (A, B)
> fromTotalPreorder1 (MkTotalPreorder R reflexive transitive totalPre) =
>   MkTotalPreorder (\ x => \ y => R (fst x) (fst y))
>              (\ x => reflexive (fst x))
>              (\ x => \ y => \ z => \ xRy => \ yRz => transitive (fst x) (fst y) (fst z) xRy yRz)
>              (\ x => \ y => totalPre (fst x) (fst y))


> from2 : {A, B : Type} -> (B -> B -> Type) -> (A, B) -> (A, B) -> Type
> from2 R x y = R (snd x) (snd y)

> ||| Total preorders on |B| induce total preorders on |(A, B)|
> fromTotalPreorder2 : {A, B : Type} -> TotalPreorder B -> TotalPreorder (A, B)
> fromTotalPreorder2 to =
>   MkTotalPreorder (from2 (R to))
>                   (\ x => reflexive to (snd x))
>                   (\ x => \ y => \ z => \ xRy => \ yRz => transitive to (snd x) (snd y) (snd z) xRy yRz)
>                   (\ x => \ y => totalPre to (snd x) (snd y))

> ---}
