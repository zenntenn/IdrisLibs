> module issues.Main

> import Data.Fin
> import Data.List
> import Data.List.Quantifiers
> import Effects
> import Effect.Exception
> import Effect.StdIO

> import LocalEffect.Exception
> import LocalEffect.StdIO

> %default total
> %auto_implicits off

> -- %logging 5

> State : Nat -> Type
> State t = (Fin (S t), Bool)

> Ctrl : (t : Nat) -> State t -> Type
> Ctrl t x = Bool

> nexts : (t : Nat) -> (x : State t) -> Ctrl t x -> List (State (S t))
> nexts t (e, _) False = [(weaken e, False), (weaken e, True), (FS e, False), (FS e, True)]
> nexts t (e, _)  True = [(weaken e, True), (weaken e, False), (FS e, True), (FS e, False)]

> Viable : {t : Nat} -> (n : Nat) -> State t -> Type
> Viable n x = Unit

> viableLemma : {t, n : Nat} -> (xs : List (State t)) -> All (Viable n) xs
> viableLemma  Nil      = Nil
> viableLemma {t} {n} (x :: xs) = () :: (viableLemma {t} {n} xs)

> Reachable : {t' : Nat} -> State t' -> Type
> Reachable x' = Unit

> showState : {t : Nat} -> State t -> String
> showState {t} (e, False) = "(" ++ show (finToNat e) ++ ",F)"
> showState {t} (e,  True) = "(" ++ show (finToNat e) ++ ",T)"

> showCtrl : {t : Nat} -> {x : State t} -> Ctrl t x -> String
> showCtrl {t} {x} False = "F"
> showCtrl {t} {x}  True = "T"

> showStateCtrl : {t : Nat} -> DPair (State t) (Ctrl t) -> String
> showStateCtrl {t} (MkDPair x y) = "(" ++ showState {t} x ++ " ** " ++ showCtrl {t} {x} y ++ ")"

> NotEmpty    : {A : Type} -> List A -> Type
> NotEmpty  Nil      = Void
> NotEmpty (a :: as) = Unit

> Good : (t : Nat) -> (x : State t) -> (n : Nat) -> (Ctrl t x) -> Type
> Good t x n y = (NotEmpty (nexts t x y), All (Viable {t = S t} n) (nexts t x y))

> GoodCtrl : (t : Nat) -> (x : State t) -> (n : Nat) -> Type
> GoodCtrl t x n = DPair (Ctrl t x) (Good t x n)

> Policy : (t : Nat) -> (n : Nat) -> Type
> Policy t Z      =  Unit
> Policy t (S m)  =  (x : State t) -> Reachable x -> Viable (S m) x -> GoodCtrl t x m

> data PolicySeq : (t : Nat) -> (n : Nat) -> Type where
>   Nil   :  {t : Nat} -> PolicySeq t Z
>   (::)  :  {t, n : Nat} -> Policy t (S n) -> PolicySeq (S t) n -> PolicySeq t (S n)

> data StateCtrlSeq : (t : Nat) -> (n : Nat) -> Type where
>   JustState : {t : Nat} -> (x : State t) -> StateCtrlSeq t Z
>   (++)      : {t, n : Nat} -> DPair (State t) (Ctrl t) -> StateCtrlSeq (S t) n -> StateCtrlSeq t (S n)

> using (t : Nat, n : Nat)
>   implementation Show (StateCtrlSeq t n) where
>     show = show' where
>       show' : {t : Nat} -> {n : Nat} -> StateCtrlSeq t n -> String
>       show' xys = "[" ++ show'' "" xys ++ "]" where
>         show'' : {t' : Nat} -> {n' : Nat} -> String -> StateCtrlSeq t' n' -> String
>         show'' {t'} {n' = Z}    acc (JustState x)     =
>           acc ++ "(" ++ showState x ++ " ** " ++ " " ++ ")"
>         show'' {t'} {n' = S m'} acc (xy ++ xys) = 
>           show'' {t' = S t'} {n' = m'} (acc ++ showStateCtrl xy ++ ", ") xys

> -- trajectories
> trjs : {t, n : Nat} -> (ps : PolicySeq t n) -> (x : State t) -> List (StateCtrlSeq t n)
> trjs {t} {n = Z}         Nil  x = [(JustState x)]
> trjs {t} {n = S m} (p :: ps') x =
>   map ((MkDPair x y) ++) ((nexts t x y) >>= (trjs {n = m} ps')) where
>     y   :  Ctrl t x
>     y   =  fst (p x () ())

> nonEmptyLemma : {t : Nat} -> (x : State t) -> NotEmpty (nexts t x True)
> nonEmptyLemma {t} (e, False) = s3 where
>   s1 : NotEmpty [(weaken e, True), (weaken e, False), (FS e, True), (FS e, False)]
>   s1 = ()
>   s2 : [(weaken e, True), (weaken e, False), (FS e, True), (FS e, False)] = nexts t (e, False) True
>   s2 = Refl
>   s3 : NotEmpty (nexts t (e, False) True)
>   s3 = replace {P = \ X => NotEmpty X} s2 s1
> nonEmptyLemma {t} (e, True) = s3 where
>   s1 : NotEmpty [(weaken e, True), (weaken e, False), (FS e, True), (FS e, False)]
>   s1 = ()
>   s2 : [(weaken e, True), (weaken e, False), (FS e, True), (FS e, False)] = nexts t (e, True) True
>   s2 = Refl
>   s3 : NotEmpty (nexts t (e, True) True)
>   s3 = replace {P = \ X => NotEmpty X} s2 s1

> pols : (t : Nat) -> (n : Nat) -> PolicySeq t n
> pols t  Z     =  Nil
> pols t (S n)  =  p :: ps where
>   p  : Policy t (S n)
>   p x r v = MkDPair True (nonEmptyLemma x, viableLemma (nexts t x True))
>   ps : PolicySeq (S t) n
>   ps = pols (S t) n

> showlong : {a : Type} -> Show a => List a -> String
> showlong xs = "[" ++ show' "" xs ++ "]" where                                                                             
>   show' acc []        = acc                                                                                         
>   show' acc [x]       = acc ++ show x                                                                               
>   show' acc (x :: xs) = show' (acc ++ show x ++ ",\n") xs

> partial
> computation : { [STDIO] } Eff ()
> computation =
>   do putStr ("enter number of steps:\n")
>      nSteps <- getNat
>      putStrLn ("computing pols ...")
>      ps   <- pure (pols Z nSteps)
>      putStrLn ("computing trjs ...")
>      mxys <- pure (trjs ps (FZ, True))
>      putStrLn ("number of trjs: " ++ show (length mxys))
>      -- putStrLn "trjs:"
>      -- putStr "  "
>      -- putStrLn (showlong mxys)
>      putStrLn ("done!")

> partial
> main : IO ()
> main = run computation


> {-


> ---}


-- Local Variables:
-- idris-packages: ("effects")
-- End:


