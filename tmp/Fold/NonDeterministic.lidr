> module papers.JFP2016.NonDeterministic

> -- import Sigma.Sigma
> -- import Sigma.Operations

> %default total
> %access public export
> %auto_implicits off


> State : (t : Nat) -> Type

> Ctrl : (t : Nat) -> (x : State t) -> Type

> nexts : (t : Nat) -> (x : State t) -> (y : Ctrl t x) -> List (State (S t))

> fmap  :  {A, B : Type} -> 
>          (A -> B) -> List A -> List B
> fmap = map         
> postulate functorSpec1  :  fmap . id = id
> postulate functorSpec2  :  {A, B, C : Type} -> {f : B -> C} -> {g : A -> B} ->
>                            fmap (f . g) = (fmap f) . (fmap g)

> Val : Type

> reward : (t : Nat) -> (x : State t) -> (y : Ctrl t x) -> (x' : State (S t)) -> Val

> rewards  : (t : Nat) -> (x : State t) -> (y : Ctrl t x) -> List Val
> rewards t x y = fmap (reward t x y) (nexts t x y)

> certain : {A : Type} -> A -> List A
> certain a = [a]

> reduce : {A : Type} -> List (List A) -> List A
> reduce = concat

> {-

> plus : Val -> Val -> Val

> zero : Val

> LTE : Val -> Val -> Type

> meas : List Val -> Val

< meas : (t : Nat) -> (x : State t) -> (List Val -> Val)


* Solving sequential decision problems

> Elem     : {A : Type} -> A -> List A -> Type
> NotEmpty : {A : Type} -> List A -> Type
> All      : {A : Type} -> (P : A -> Type) -> List A -> Type
> tagElem  : {A : Type} -> (ma : List A) -> List (Sigma A (\ a => a `Elem` ma))

> allElemSpec0                 :  {A : Type} -> {P : A -> Type} ->
>                                 (a : A) -> (ma : List A) -> All P ma -> a `Elem` ma -> P a

> postulate elemNotEmptySpec0  :  {A : Type} -> 
>                                 (a : A) -> (ma : List A) -> a `Elem` ma -> NotEmpty ma

> postulate elemNotEmptySpec1  :  {A : Type} -> 
>                                 (ma : List A) -> NotEmpty ma -> Sigma A (\ a => a `Elem` ma)


> postulate tagElemSpec        :  {A : Type} -> (ma : List A) -> fmap outl (tagElem ma) = ma


* Viability

> Viable : {t : Nat} -> (n : Nat) -> State t -> Type

> postulate viableSpec0 : {t : Nat} ->
>                         (x : State t) -> Viable Z x

> Good : (t : Nat) -> (x : State t) -> (n : Nat) -> (Ctrl t x) -> Type
> Good t x n y = (NotEmpty (nexts t x y), All (Viable {t = S t} n) (nexts t x y))

> GoodCtrl : (t : Nat) -> (x : State t) -> (n : Nat) -> Type
> GoodCtrl t x n = Sigma (Ctrl t x) (Good t x n)
> -- GoodCtrl t x n = Sigma (Ctrl t x) (\ y => (NotEmpty (nexts t x y), All (Viable {t = S t} n) (nexts t x y)))

> viableSpec1 : {t : Nat} -> {n : Nat} ->
>               (x : State t) -> Viable (S n) x -> GoodCtrl t x n

> postulate viableSpec2 : {t : Nat} -> {n : Nat} ->
>                         (x : State t) -> GoodCtrl t x n -> Viable (S n) x

> ctrl : {t, n : Nat} -> {x : State t} -> GoodCtrl t x n -> Ctrl t x
> ctrl (MkSigma y _) = y

> -- good : {t, n : Nat} -> {x : State t} -> (y : GoodCtrl t x n) -> Good t x n (ctrl y)
> -- good (MkSigma _ p) = p

> allViable : {t, n : Nat} -> {x : State t} -> (y : GoodCtrl t x n) -> All (Viable n) (nexts t x (ctrl y)) 
> allViable (MkSigma _ p) = snd p


* Reachability

> Reachable : {t' : Nat} -> State t' -> Type

> postulate reachableSpec0 : (x : State Z) -> Reachable x

> reachableSpec1  :  {t : Nat} -> (x : State t) -> Reachable x -> (y : Ctrl t x) -> All Reachable (nexts t x y)

> Pred : {t : Nat} -> State t -> State (S t) -> Type
> Pred {t} x x'  =  Sigma (Ctrl t x) (\ y => x' `Elem` nexts t x y)

> ReachablePred : {t : Nat} -> State t -> State (S t) -> Type
> ReachablePred x x'  = (Reachable x, x `Pred` x')

> postulate reachableSpec2  :  {t : Nat} -> (x' : State (S t)) -> Reachable x' -> Sigma (State t) (\ x => x `ReachablePred` x')


* Policies and policy sequences

> Policy : (t : Nat) -> (n : Nat) -> Type
> Policy t Z      =  Unit
> Policy t (S m)  =  (x : State t) -> Reachable x -> Viable (S m) x -> GoodCtrl t x m

> data PolicySeq : (t : Nat) -> (n : Nat) -> Type where
>   Nil   :  {t : Nat} -> 
>            PolicySeq t Z
>   (::)  :  {t, n : Nat} -> 
>            Policy t (S n) -> PolicySeq (S t) n -> PolicySeq t (S n)


* The value of policy sequences

> PossibleNextState  :  {t : Nat} -> 
>                       (x  : State t) -> (y : Ctrl t x) -> Type
> PossibleNextState {t} x y = Sigma (State (S t)) (\ x' => x' `Elem` (nexts t x y))

> mutual

>   sval  :  {t, m : Nat} -> 
>            (x  : State t) -> (r  : Reachable x) -> (v  : Viable (S m) x) ->
>            (gy  : GoodCtrl t x m) -> (ps : PolicySeq (S t) m) ->
>            PossibleNextState x (ctrl gy) -> Val
>   sval {t} {m} x r v gy ps (MkSigma x' x'emx') = reward t x y x' `plus` val x' r' v' ps where
>     y   : Ctrl t x
>     y   = ctrl gy
>     mx' : List (State (S t))
>     mx' = nexts t x y
>     ar' : All Reachable mx'
>     ar' = reachableSpec1 x r y
>     av' : All (Viable m) mx'
>     av' = allViable gy
>     r'  : Reachable x'
>     r'  = allElemSpec0 x' mx' ar' x'emx'
>     v'  : Viable m x'
>     v'  = allElemSpec0 x' mx' av' x'emx'

>   val  :  {t, n : Nat} -> 
>           (x : State t) -> Reachable x -> Viable n x -> PolicySeq t n -> Val
>   val {t} {n = Z} x r v ps = zero
>   val {t} {n = S m} x r v (p :: ps) = meas (fmap (sval x r v gy ps) (tagElem mx')) where
>     gy   :  GoodCtrl t x m
>     gy   =  p x r v
>     y    :  Ctrl t x
>     y    =  ctrl gy
>     mx'  :  List (State (S t))
>     mx'  =  nexts t x y


* Optimality of policy sequences

> OptPolicySeq  :  {t, n : Nat} -> 
>                  PolicySeq t n -> Type
> 
> OptPolicySeq {t} {n} ps  =  (ps' : PolicySeq t n) ->
>                             (x : State t) -> (r : Reachable x) -> (v : Viable n x) ->
>                             val x r v ps' `LTE` val x r v ps


* Optimal extensions of policy sequences

> OptExt  :  {t, m : Nat} -> 
>            PolicySeq (S t) m -> Policy t (S m) -> Type
> OptExt {t} {m} ps p  =  (p' : Policy t (S m)) ->
>                         (x : State t) -> (r : Reachable x) -> (v : Viable (S m) x) ->
>                         val x r v (p' :: ps) `LTE` val x r v (p :: ps)

> cval  :  {t, n : Nat} -> 
>          (x  : State t) -> (r  : Reachable x) -> (v  : Viable (S n) x) ->
>          (ps : PolicySeq (S t) n) -> GoodCtrl t x n -> Val
> cval {t} x r v ps gy = meas (fmap (sval x r v gy ps) (tagElem mx')) where
>   y    :  Ctrl t x
>   y    =  ctrl gy
>   mx'  :  List (State (S t))
>   mx'  =  nexts t x y

> cvalargmax  :  {t, n : Nat} -> 
>                (x  : State t) -> (r  : Reachable x) -> (v  : Viable (S n) x) ->
>                (ps : PolicySeq (S t) n) -> GoodCtrl t x n

> optExt  :  {t, n : Nat} -> 
>            PolicySeq (S t) n -> Policy t (S n)
> optExt {t} {n} ps = p where
>   p : Policy t (S n)
>   p x r v = cvalargmax x r v ps


* Generic machine checkable backwards induction

> backwardsInduction : (t : Nat) -> (n : Nat) -> PolicySeq t n
> backwardsInduction t  Z     =  Nil
> backwardsInduction t (S n)  =  optExt ps :: ps where
>   ps : PolicySeq (S t) n
>   ps = backwardsInduction (S t) n


> ---}


[1] Bellman, Richard; "Dynamic Programming", Princeton University Press,
    1957

[2] Ionescu, Cezar; "Vulnerability Modelling and Monadic Dynamical
    Systems", Freie Universitaet Berlin, 2009
