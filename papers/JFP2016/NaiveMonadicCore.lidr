> module papers.JFP2016.NaiveMonadicCore

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


* Optimality of policy sequences

> OptPolicySeq  :  {t, n : Nat} -> 
>                  PolicySeq t n -> Type
> OptPolicySeq {t} {n} ps  =  (ps' : PolicySeq t n) -> (x : State t) -> val x ps' `LTE` val x ps


* Optimal extensions of policy sequences

> OptExt : {t, m : Nat} -> 
>          PolicySeq (S t) m -> Policy t -> Type
> OptExt {t} {m} ps p  =  (p' : Policy t) -> (x : State t) -> val x (p' :: ps) `LTE` val x (p :: ps)

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


> {-

> ---}
