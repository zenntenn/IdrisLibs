> module Fold.MonadicCore

> import Sigma.Sigma
> import Sigma.Operations

> %default total
> %access public export
> %auto_implicits off


* Sequential decision processes

> State : (t : Nat) -> Type

> Ctrl : (t : Nat) -> (x : State t) -> Type

> M : Type -> Type

> nexts : (t : Nat) -> (x : State t) -> (y : Ctrl t x) -> M (State (S t))

> fmap  :  {A, B : Type} -> 
>          (A -> B) -> M A -> M B
> postulate functorSpec1  :  fmap . id = id
> postulate functorSpec2  :  {A, B, C : Type} -> {f : B -> C} -> {g : A -> B} ->
>                            fmap (f . g) = (fmap f) . (fmap g)


* Sequential decision problems

> Val : Type

> reward : (t : Nat) -> (x : State t) -> (y : Ctrl t x) -> (x' : State (S t)) -> Val

> plus : Val -> Val -> Val

> zero : Val

> LTE : Val -> Val -> Type

> meas : M Val -> Val


* Solving sequential decision problems

> Elem     : {A : Type} -> A -> M A -> Type
> NotEmpty : {A : Type} -> M A -> Type
> All      : {A : Type} -> (P : A -> Type) -> M A -> Type

> allElemSpec0       :  {A : Type} -> {P : A -> Type} ->
>                       (a : A) -> (ma : M A) -> All P ma -> a `Elem` ma -> P a
> postulate elemNotEmptySpec0  :  {A : Type} -> 
>                                 (a : A) -> (ma : M A) -> a `Elem` ma -> NotEmpty ma
> postulate elemNotEmptySpec1  :  {A : Type} -> 
>                                 (ma : M A) -> NotEmpty ma -> Sigma A (\ a => a `Elem` ma)

> tagElem      :  {A : Type} -> (ma : M A) -> M (Sigma A (\ a => a `Elem` ma))
> postulate tagElemSpec  :  {A : Type} -> (ma : M A) -> fmap outl (tagElem ma) = ma


* Viability

> Viable       :  {t : Nat} -> 
>                 (n : Nat) -> State t -> Type

> Good            :  (t : Nat) -> (x : State t) -> (n : Nat) -> (Ctrl t x) -> Type
> Good t x n y    =  (NotEmpty (nexts t x y), All (Viable {t = S t} n) (nexts t x y))
>
> GoodCtrl        :  (t : Nat) -> (x : State t) -> (n : Nat) -> Type
> GoodCtrl t x n  =  Sigma (Ctrl t x) (Good t x n)

> postulate viableSpec0  :  {t : Nat} -> 
>                           (x : State t) -> Viable Z x
> viableSpec1  :  {t, n : Nat} -> 
>                 (x : State t) -> Viable (S n) x -> GoodCtrl t x n
> postulate viableSpec2  :  {t, n : Nat} -> 
>                           (x : State t) -> GoodCtrl t x n -> Viable (S n) x

> ctrl : {t, n : Nat} -> {x : State t} -> 
>        GoodCtrl t x n -> Ctrl t x
> ctrl (MkSigma y _) = y

> allViable : {t, n : Nat} -> {x : State t} -> 
>             (y : GoodCtrl t x n) -> All (Viable n) (nexts t x (ctrl y)) 
> allViable (MkSigma _ p) = snd p


* Reachability

> Reachable       :  {t' : Nat} -> 
>                    State t' -> Type

> Pred           :  {t : Nat} -> 
>                   State t -> State (S t) -> Type
> Pred {t} x x'  =  Sigma (Ctrl t x) (\ y => x' `Elem` nexts t x y)

> ReachablePred       :  {t : Nat} -> 
>                        State t -> State (S t) -> Type
> ReachablePred x x'  =  (Reachable x, x `Pred` x')

> postulate reachableSpec0  :  (x : State Z) -> Reachable x
> reachableSpec1  :  {t : Nat} -> 
>                    (x : State t) -> Reachable x -> (y : Ctrl t x) -> All Reachable (nexts t x y)
> postulate reachableSpec2  :  {t : Nat} -> 
>                              (x' : State (S t)) -> Reachable x' -> Sigma (State t) (\ x => x `ReachablePred` x')


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

> PossibleNextState : {t : Nat} -> 
>                     (x  : State t) -> (y : Ctrl t x) -> Type
> PossibleNextState {t} x y = Sigma (State (S t)) (\ x' => x' `Elem` (nexts t x y))

> mutual

>   val  :  {t, n : Nat} -> 
>           (x : State t) -> Reachable x -> Viable n x -> PolicySeq t n -> Val
>   val {t} {n = Z} x r v ps           =  zero
>   val {t} {n = S m} x r v (p :: ps)  =  meas (fmap (sval x r v gy ps) (tagElem mx')) where
>     gy   : GoodCtrl t x m;;   gy   = p x r v
>     y    : Ctrl t x;;         y    = ctrl gy
>     mx'  : M (State (S t));;  mx'  = nexts t x y
>
>   sval  :  {t, m : Nat} -> 
>            (x  : State t) -> (r  : Reachable x) -> (v  : Viable (S m) x) ->
>            (gy  : GoodCtrl t x m) -> (ps : PolicySeq (S t) m) ->
>            PossibleNextState x (ctrl gy) -> Val
>   sval {t} {m} x r v gy ps (MkSigma x' x'emx') = reward t x y x' `plus` val x' r' v' ps where
>     y    : Ctrl t x;;            y    = ctrl gy
>     mx'  : M (State (S t));;     mx'  = nexts t x y
>     ar'  : All Reachable mx';;   ar'  = reachableSpec1 x r y
>     av'  : All (Viable m) mx';;  av'  = allViable gy
>     r'   : Reachable x';;        r'   = allElemSpec0 x' mx' ar' x'emx'
>     v'   : Viable m x';;         v'   = allElemSpec0 x' mx' av' x'emx'


* Optimality of policy sequences

> OptPolicySeq : {t, n : Nat} -> 
>                PolicySeq t n -> Type
> OptPolicySeq {t} {n} ps  =  (x : State t) -> (r : Reachable x) -> (v : Viable n x) ->
>                             (ps' : PolicySeq t n) ->
>                             val x r v ps' `LTE` val x r v ps


* Optimal extensions of policy sequences

> OptExt : {t, m : Nat} -> 
>          PolicySeq (S t) m -> Policy t (S m) -> Type
> OptExt {t} {m} ps p  =  (x : State t) -> (r : Reachable x) -> (v : Viable (S m) x) ->
>                         (p' : Policy t (S m)) ->
>                         val x r v (p' :: ps) `LTE` val x r v (p :: ps)

> cval  :  {t, n : Nat} -> 
>          (x  : State t) -> (r  : Reachable x) -> (v  : Viable (S n) x) ->
>          (ps : PolicySeq (S t) n) -> GoodCtrl t x n -> Val
> cval {t} x r v ps gy = meas (fmap (sval x r v gy ps) (tagElem mx')) where
>   y    : Ctrl t x;;         y    = ctrl gy
>   mx'  : M (State (S t));;  mx'  = nexts t x y

> cvalargmax  :  {t, n : Nat} -> 
>                (x  : State t) -> (r  : Reachable x) -> (v  : Viable (S n) x) ->
>                (ps : PolicySeq (S t) n) -> GoodCtrl t x n

> optExt : {t, n : Nat} -> 
>          PolicySeq (S t) n -> Policy t (S n)
> optExt {t} {n} ps = p where
>   p : Policy t (S n);;  p x r v = cvalargmax x r v ps


* Generic machine checkable backwards induction

> backwardsInduction : (t : Nat) -> (n : Nat) -> PolicySeq t n
> backwardsInduction t  Z     =  Nil
> backwardsInduction t (S n)  =  let ps = backwardsInduction (S t) n in optExt ps :: ps

> {-

> ---}
 