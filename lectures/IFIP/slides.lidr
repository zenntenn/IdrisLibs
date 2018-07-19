> module Slides

> -- import Data.So
> import Data.Vect
> -- import Data.List
> -- import Data.List.Quantifiers

> import Sigma.Sigma
> -- import Rel.TotalPreorder
> -- import NonNegDouble.NonNegDouble
> -- import NonNegDouble.BasicOperations
> -- import Nat.LTEProperties

> %default total
> %access public export
> %auto_implicits off

> %hide index

* Vector indexing and lookup

> index   :  {X : Type} -> {n : Nat} -> 
>            Fin n -> Vect n X -> X

> Injective2 : {X : Type} -> {n : Nat} -> Vect n X -> Type
> Injective2 {n} xs = (i : Fin n) -> (j : Fin n) -> Not (i = j) -> Not (index i xs = index j xs)

> lookup  :  {X : Type} -> {n : Nat} -> 
>            (x : X) -> (xs : Vect n X) -> Elem x xs -> Fin n

> lookup'  :  {X : Type} -> {n : Nat} -> 
>             (x : X) -> (xs : Vect n X) -> List (Fin n)

> ilSpec  :  {X : Type} -> {n : Nat} -> 
>            (x : X) -> (xs : Vect n X) -> (p : Elem x xs) -> index (lookup x xs p) xs = x

> liSpec  :  {X : Type} -> {n : Nat} -> 
>            (k : Fin n) -> (xs : Vect n X) -> (p : Injective2 xs) -> (q : Elem (index k xs) xs) -> lookup (index k xs) xs q = k

> indexSpec  :  {X : Type} -> {n : Nat} -> 
>               (k : Fin n) -> (xs : Vect n X) -> Elem (index k xs) xs

> index'   :  {X : Type} -> {n : Nat} -> 
>             (k : Fin n) -> (xs : Vect n X) -> Sigma X (\ x => Elem x xs) 

> liSpec'  :  {X : Type} -> {n : Nat} -> 
>             (k : Fin n) -> (xs : Vect n X) -> (p : Injective2 xs) -> lookup (index k xs) xs (indexSpec k xs) = k

* Finite function maximization

> M : Type -> Type

> monadM : Functor M

> lala : {A, B : Type} -> (A -> B) -> M A -> M B
> lala = map



> {-

> Set : Type
> Set = Type

> Prop : Type -> Type
> Prop A = A -> Type

> All : (A : Type) -> (P : Prop A) -> Type
> All A P = (a : A) -> P a 


* Properties

> pair : Type -> Type -> Type
> pair A B = (A, B)

> Domain : (f : c -> d) -> Type
> Domain {c} f = c

> Codomain : (f : c -> d) -> Type
> Codomain {d} f = d

> BoundedBy : Nat -> List Nat -> Type
> BoundedBy n ms = All (\ m => m `LTE` n) ms

> simpleLemma : BoundedBy 42 [0,42,1]
> simpleLemma = [LTEZero, reflexiveLTE 42, LTESucc LTEZero]


> A : Type
> a : A
> P : A -> Type
> pa : P a
> prf : (a : A ** P a)


* Domain specific notions

> Injective : (f : c -> d) -> Type
> Injective f = (x, y : Domain f) -> f x = f y -> x = y

> Reflexive : {A : Type} -> (r : A -> A -> Type) -> Type
> Reflexive {A} r = (a : A) -> r a a 

> Decidable : {A : Type} -> (P : A -> Type) -> Type
> Decidable {A} P = (a : A) -> Either (P a) (Not (P a)) 

** Sequential decision problems and policy advice

> State : Type

> Ctrl : (x : State) -> Type

> Policy : Type
> Policy = (x : State) -> Ctrl x

> Val           :  Type
> ValLTE        :  Val -> Val -> Type
> totalPreorder :  TotalPreorder ValLTE

> val           :  State -> Vect n Policy -> Val

>
> Optimal  :  Vect n Policy -> Type
> Optimal {n} ps  =  (x : State) -> (ps' : Vect n Policy) -> 
>                    val x ps' `ValLTE` val x ps

> Sustainable    :  (x' : State) -> Type
> AvoidableFrom  :  (x' : State) -> (x : State) -> Type


* Aims, challenges

** Modelling

> data DoubleLTE : Double -> Double -> Type where
>   MkDoubleLTE : {x : Double} -> {y : Double} -> So (x <= y) -> DoubleLTE x y

> Agent   :  Type
> data Car  =  ElectricCar | GasolineCar 
> 
> Prob    :  Type -> Type
> prob    :  Prob t -> t -> Double

> buy      :  Agent -> Prob Car
> income   :  Agent -> Double

> Spec     :  (a, a' : Agent) -> income a `DoubleLTE` income a' ->
>             prob (buy a) ElectricCar `DoubleLTE` prob (buy a') ElectricCar  

> NonNegDoubleLTE : NonNegDouble -> NonNegDouble -> Type
> NonNegDoubleLTE x y = DoubleLTE (toDouble x) (toDouble y) 

> pLL    :  Double  -- Probability of being able to implement low emission 
>                   -- policies when the current emissions are low
>
> pLH    :  Double  -- Probability of being able to implement low emission
>                   -- policies when the current emissions are high
>
> Spec1  :  (0 `DoubleLTE` pLL, pLL `DoubleLTE` 1)
> Spec2  :  (0 `DoubleLTE` pLH, pLH `DoubleLTE` 1)
> Spec3  :  pLH `DoubleLTE` pLL


* Assumptions, beliefs

** We can introduce assumptions ...

> postulate
> max      :  (f : d -> c) -> (tp : TotalPreorder cLTE) -> Codomain f
>
> postulate
> maxSpec  :  (f : d -> c) -> (tp : TotalPreorder cLTE) ->
>             (x : Domain f) -> (f x) `cLTE` (max f tp)

> postulate Pub           :  Type
>
> postulate Drink         :  Pub -> Type
>
> postulate exclMiddle    :  Either (All Pub Drink) (Not (All Pub Drink))
>
> postulate choice        :  Pub
>
> postulate notAllExists  :  Not (All Pub Drink) -> (x : Pub ** Not (Drink x))


** ... and build theories


> DrinkerLemma : (x : Pub ** Drink x -> All Pub Drink)

> DrinkerLemma with (exclMiddle)
>   | Left  prf = (choice ** \ dp => prf)
>   | Right prf = (p ** \ dp => void (ndp dp)) where
>       p   : Pub
>       p   = fst (notAllExists prf)
>       ndp : Not (Drink p)
>       ndp = snd (notAllExists prf) 

> ---}
