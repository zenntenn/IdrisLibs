> module Fold.NaiveMonadicCore

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
> tagElem  : {A : Type} -> (ma : M A) -> M (Sigma A (\ a => a `Elem` ma))

> allElemSpec0                 :  {A : Type} -> {P : A -> Type} ->
>                                 (a : A) -> (ma : M A) -> All P ma -> a `Elem` ma -> P a

> postulate elemNotEmptySpec0  :  {A : Type} -> 
>                                 (a : A) -> (ma : M A) -> a `Elem` ma -> NotEmpty ma

> postulate elemNotEmptySpec1  :  {A : Type} -> 
>                                 (ma : M A) -> NotEmpty ma -> Sigma A (\ a => a `Elem` ma)

> postulate tagElemSpec        :  {A : Type} -> (ma : M A) -> fmap outl (tagElem ma) = ma


* Policies and policy sequences

> Policy : (t : Nat) -> Type
> Policy t = (x : State t) -> Ctrl t x

> data PolicySeq : (t : Nat) -> (n : Nat) -> Type where
>   Nil   :  {t : Nat} -> 
>            PolicySeq t Z
>   (::)  :  {t, n : Nat} -> 
>            Policy t -> PolicySeq (S t) n -> PolicySeq t (S n)

> foldPolicySeq : {X : Nat -> Nat -> Type} ->
>                 ((t : Nat) -> X t Z) ->
>                 ((t : Nat) -> (n : Nat) -> Policy t -> X (S t) n -> X t (S n)) ->
>                 (t : Nat) -> (n : Nat) -> PolicySeq t n -> X t n
> foldPolicySeq x0 f t Z Nil = x0 t
> foldPolicySeq x0 f t (S n) Nil impossible
> foldPolicySeq x0 f t (S n) (p :: ps) = f t n p (foldPolicySeq x0 f (S t) n ps)

* The value of policy sequences

> val : {t, n : Nat} -> 
>       (x : State t) -> PolicySeq t n -> Val
> val {t} {n = Z} x ps = zero
> val {t} {n = S m} x (p :: ps) = meas (fmap f mx') where
>   y     :  Ctrl t x
>   y     =  p x
>   f     :  State (S t) -> Val
>   f x'  =  reward t x y x' `plus` val x' ps 
>   mx'   :  M (State (S t))
>   mx'   =  nexts t x y

> {-
> valFold : (t : Nat) -> (n : Nat) -> PolicySeq t n -> State t -> Val
> valFold t Z Nil = const zero
> valFold t (S n) (p :: ps) = g t n p (valFold (S t) n ps) where
>   g : (t : Nat) -> (n : Nat) -> (p : Policy t) -> (State (S t) -> Val) -> State t -> Val
>   g t n p valSt x = meas (fmap f mx') where
>     y : Ctrl t x
>     y = p x
>     f : State (S t) -> Val
>     f x' = reward t x y x' `plus` valSt x'
>     mx' : M (State (S t))
>     mx' = nexts t x y
> -}    

> valFold : (t : Nat) -> (n : Nat) -> PolicySeq t n -> State t -> Val
> valFold t n ps = foldPolicySeq {X = \ t => \ n => State t -> Val} (\ t => \ x => zero) g t n ps where
>   g : (t : Nat) -> (n : Nat) -> (p : Policy t) -> (State (S t) -> Val) -> State t -> Val
>   g t n p valSt x = meas (fmap f mx') where
>     y : Ctrl t x
>     y = p x
>     f : State (S t) -> Val
>     f x' = reward t x y x' `plus` valSt x'
>     mx' : M (State (S t))
>     mx' = nexts t x y


* Optimality of policy sequences

> OptPolicySeq  :  {t, n : Nat} -> 
>                  PolicySeq t n -> Type
> OptPolicySeq {t} {n} ps  =  (x : State t) -> (ps' : PolicySeq t n) -> val x ps' `LTE` val x ps


* Optimal extensions of policy sequences

> OptExt : {t, m : Nat} -> 
>          PolicySeq (S t) m -> Policy t -> Type
> OptExt {t} {m} ps p  =  (x : State t) -> (p' : Policy t) -> val x (p' :: ps) `LTE` val x (p :: ps)

> cval : {t, n : Nat} -> 
>        (x  : State t) -> (ps : PolicySeq (S t) n) -> Ctrl t x -> Val
> cval {t} {n} x ps y = meas (fmap f mx') where
>   f    :  State (S t) -> Val
>   f x' =  reward t x y x' `plus` val x' ps 
>   mx'  :  M (State (S t))
>   mx'  =  nexts t x y

> cvalargmax : {t, n : Nat} -> 
>              (x  : State t) -> (ps : PolicySeq (S t) n) -> Ctrl t x

> optExt : {t, n : Nat} -> 
>          PolicySeq (S t) n -> Policy t
> optExt {t} ps = p where
>   p : Policy t
>   p x = cvalargmax x ps


* Generic machine checkable backwards induction

> backwardsInduction : (t : Nat) -> (n : Nat) -> PolicySeq t n
> backwardsInduction t  Z     =  Nil
> backwardsInduction t (S n)  =  optExt ps :: ps where
>   ps : PolicySeq (S t) n
>   ps = backwardsInduction (S t) n

> paraNat : {X : Nat -> Type} -> (x0 : X 0) -> (f : (n : Nat) -> X n -> X (S n)) -> (n : Nat) -> X n
> paraNat x0 f Z = x0
> paraNat x0 f (S n) = f n (paraNat x0 f n)

> foldNat : {X : Nat -> Nat -> Type} -> 
>           (x0 : (t : Nat) -> X t Z) -> 
>           (f : (t : Nat) -> (n : Nat) -> X (S t) n -> X t (S n)) -> 
>           (t : Nat) -> (n : Nat) -> X t n
> foldNat x0 f t Z     = x0 t
> foldNat x0 f t (S n) = f t n (foldNat x0 f (S t) n)

> bif : (t : Nat) -> (n : Nat) -> PolicySeq t n
> bif t n = foldNat x0 f t n where
>   x0 : (t : Nat) -> PolicySeq t Z
>   x0 = \ t => Nil
>   f  : (t : Nat) -> (n : Nat) -> PolicySeq (S t) n -> PolicySeq t (S n)
>   f  t n ps = optExt ps :: ps

< initalPolicySeq : [Nil : PolicySeq t Z, (::) : Policy t -> PolicySeq (S t) n -> PolicySeq t (S n)]

> coPolicySeq : {X : Nat -> Nat -> Type} -> ((t : Nat) -> (n : Nat) -> X t (S n) -> Either (X t Z) (Policy t, X (S t) n)) ->
>               (t : Nat) -> (n : Nat) -> (x : Either (X t Z) (X t (S n))) -> PolicySeq t n
> coPolicySeq f t Z (Left x)   = Nil
> coPolicySeq f t (S n) (Right x)  with (f t (S n) x)
>       | Left x' = ?l
>       | Right (pol, x') = pol :: coPolicySeq f (S t) n (Right x')

> {-

> ---}
