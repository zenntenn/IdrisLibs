> module List.Operations

> import Data.List
> import Data.List.Quantifiers
> import Syntax.PreorderReasoning

> import Sigma.Sigma
> import Fun.Operations
> -- import NumRefinements
> import Rel.TotalPreorder
> import Rel.TotalPreorderOperations

> %default total
> %access public export
> %auto_implicits on


* |List| is a functor:

> ||| fmap
> fmap : {A, B : Type} -> (A -> B) -> List A -> List B
> fmap = map


* |List| is a monad:

> ||| ret
> ret : {A : Type} -> A -> List A
> ret = pure

> ||| bind
> bind : {A, B : Type} -> List A -> (A -> List B) -> List B
> bind = (>>=)


* |List| is a container monad:

> |||
> NonEmpty    : {A : Type} -> List A -> Type
> NonEmpty  Nil      = Void
> NonEmpty (a :: as) = Unit

> idThere : {A : Type} ->
>           (a : A) -> (as : List A) ->
>           Sigma A (\ x => x `Elem` as) -> Sigma A (\ x => x `Elem` (a :: as))
> idThere a as (MkSigma x p) = MkSigma x (There p)

> ||| Tagging
> tagElem  :  {A : Type} -> (as : List A) -> List (Sigma A (\ a => a `Elem` as))
> tagElem Nil = Nil
> tagElem {A} (x :: xs) = (MkSigma x Here) :: (map (idThere x xs) (tagElem xs))


* Show

> implementation Show (Elem a as) where
>   show = show' where
>     show' : {A : Type} -> {a : A} -> {as : List A} -> Elem a as -> String
>     show'  Here     = "Here"
>     show' (There p) = "There" ++ show' p

> showlong : Show a => List a -> String
> showlong xs = "  [" ++ show' "" xs ++ "]" where                                                                             
>   show' acc []        = acc                                                                                         
>   show' acc [x]       = acc ++ show x                                                                               
>   show' acc (x :: xs) = show' (acc ++ show x ++ ",\n" ++ "   ") xs


* Reduction operators

> |||
> max : {A : Type} -> {R : A -> A -> Type} -> 
>       TotalPreorder R -> (as : List A) -> List.Operations.NonEmpty as -> A
> max tp       Nil        p = absurd p
> max tp (a :: Nil)       _ = a
> max tp (a :: a' :: abs) _ with (max tp (a' :: abs) ())
>   | m with (totalPre tp a m)
>     | (Left _)  = m
>     | (Right _) = a

> |||
> argmaxMax : {A, B : Type} -> {R : B -> B -> Type} -> 
>             TotalPreorder R -> (abs : List (A, B)) -> List.Operations.NonEmpty abs -> (A, B)
> argmaxMax tp       Nil                   p = absurd p
> argmaxMax tp ((a, b) :: Nil)             _ = (a, b)
> argmaxMax tp ((a, b) :: (a', b') :: abs) _ with (argmaxMax tp ((a', b') :: abs) ())
>   | (argmax, max) with (totalPre tp b max)
>     | (Left _)  = (argmax, max)
>     | (Right _) = (a, b)

> |||
> min : {A : Type} -> {R : A -> A -> Type} -> 
>       TotalPreorder R -> (as : List A) -> List.Operations.NonEmpty as -> A
> {-
> min tp       Nil        p = absurd p
> min tp (a :: Nil)       _ = a
> min tp (a :: a' :: abs) _ with (min tp (a' :: abs) ())
>   | m with (totalPre tp a m)
>     | (Left _)  = a
>     | (Right _) = m
> -}
> min tp       Nil        p = absurd p
> min tp (a :: Nil)       _ = a
> min tp (a :: a' :: abs) _ with (totalPre tp a a')
>   | (Left  _) = assert_total (min tp (a  :: abs) ())
>   | (Right _) = assert_total (min tp (a' :: abs) ())


> |||
> argminMin : {A, B : Type} -> {R : B -> B -> Type} -> 
>             TotalPreorder R -> (abs : List (A, B)) -> List.Operations.NonEmpty abs -> (A, B)
> argminMin tp       Nil                   p = absurd p
> argminMin tp ((a, b) :: Nil)             _ = (a, b)
> argminMin tp ((a, b) :: (a', b') :: abs) _ with (argminMin tp ((a', b') :: abs) ())
>   | (argmin, min) with (totalPre tp b min)
>     | (Left _)  = (a, b)
>     | (Right _) = (argmin, min)


> {-

> |||
> argmaxMax : {A, B : Type} -> TotalPreorder B -> (abs : List (A, B)) -> List.Operations.NonEmpty abs -> (A, B)
> argmaxMax tp       Nil                   p = absurd p
> argmaxMax tp ((a, b) :: Nil)             _ = (a, b)
> argmaxMax tp ((a, b) :: (a', b') :: abs) _ with (argmaxMax tp ((a', b') :: abs) ())
>   | (argmax, max) with (totalPre tp b max)
>     | (Left _)  = (argmax, max)
>     | (Right _) = (a, b)

> |||
> argminMin : {A, B : Type} -> TotalPreorder B -> (abs : List (A, B)) -> List.Operations.NonEmpty abs -> (A, B)
> argminMin tp       Nil                   p = absurd p
> argminMin tp ((a, b) :: Nil)             _ = (a, b)
> argminMin tp ((a, b) :: (a', b') :: abs) _ with (argminMin tp ((a', b') :: abs) ())
>   | (argmin, min) with (totalPre tp b min)
>     | (Left _)  = (a, b)
>     | (Right _) = (argmin, min)

> -}

> |||
> sumMapSnd : {A, B : Type} -> (Num B) => List (A, B) -> B
> sumMapSnd abs = sum (map snd abs)

> |||
> mapIdRightMult : {A, B : Type} -> (Num B) => (List (A, B), B) -> List (A, B)
> mapIdRightMult (abs, b) = map (cross id (* b)) abs

> |||
> mvMult : {A, A', B : Type} -> (Num B) => List (A, B) -> (A -> List (A', B)) -> List (A', B)
> mvMult abs f = concat (map (mapIdRightMult . (cross f id)) abs)
> -- mvMult            Nil  f = Nil
> -- mvMult ((a, b) :: abs) f = mapIdRightMult (f a, b) ++ mvMult abs f

> |||
> prods : {B : Type} -> (Num B) => List (B, B) -> List B
> prods = map (uncurry (*))

> |||
> sumProds : {B : Type} -> (Num B) => List (B, B) -> B
> sumProds Nil = 0
> sumProds ((b,b') :: bbs) = b * b' + sumProds bbs


* Filtering

> ||| Filters a list on a decidable property and pairs elements with proofs
> filterTagSigma : {A : Type} ->
>                  {P : A -> Type} ->
>                  ((a : A) -> Dec (P a)) ->
>                  List A -> 
>                  List (Sigma A P)
> filterTagSigma d1P Nil = Nil
> filterTagSigma d1P (a :: as) with (filterTagSigma d1P as)
>   | tail with (d1P a)
>     | (Yes p) = (MkSigma a p) :: tail
>     | (No  _) = tail

> ||| Filters a list on a decidable property and pairs elements with proofs
> filterTagSubset : {A : Type} ->
>                   {P : A -> Type} ->
>                   ((a : A) -> Dec (P a)) ->
>                   List A -> 
>                   List (Subset A P)
> filterTagSubset d1P Nil = Nil
> filterTagSubset d1P (a :: as) with (filterTagSubset d1P as)
>   | tail with (d1P a)
>     | (Yes p) = (Element a p) :: tail
>     | (No  _) = tail


* Ad-hoc filtering

> |||
> discardZeroes : {B : Type} -> (Num B, DecEq B) => List B -> List B
> discardZeroes  Nil      = Nil
> discardZeroes (b :: bs) with (decEq b 0)
>   | (Yes _) = discardZeroes bs
>   | (No _)  = b :: discardZeroes bs

> |||
> discardBySndZero : {A, B : Type} -> (Num B, DecEq B) => List (A, B) -> List (A, B)
> discardBySndZero  Nil      = Nil
> discardBySndZero (ab :: abs) with (decEq (snd ab) 0)
>   | (Yes _) = discardBySndZero abs
>   | (No _)  = ab :: discardBySndZero abs

> |||
> discardBySndZeroEq : {A, B : Type} -> (Num B, Eq B) => List (A, B) -> List (A, B)
> discardBySndZeroEq  Nil      = Nil
> discardBySndZeroEq (ab :: abs) with ((snd ab) == 0)
>   |  True = discardBySndZeroEq abs
>   | False = ab :: discardBySndZeroEq abs
