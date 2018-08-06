> module InfiniteHorizonSequentialDecisionProblems.Lala

> import Data.Vect
> import Syntax.PreorderReasoning

> import Finite.Predicates
> import Finite.Operations
> import Finite.Properties
> import Vect.Operations
> import Vect.Properties
> import Pair.Properties

> %default total
> %access public export
> %auto_implicits off


* ---------
* Sequences
* ---------

> Seq : Type -> Type
> Seq A = Nat -> A

> head : {A : Type} -> Seq A -> A
> head f = f Z

> tail : {A : Type} -> Seq A -> Seq A
> tail f = f . S

> cons : {A : Type} -> A -> Seq A -> Seq A
> cons a f    Z  = a
> cons a f (S n) = f n 

> headLemma : {A : Type} -> (a : A) -> (f : Seq A) -> head (cons a f) = a
> headLemma a f = Refl

> tailLemma : {A : Type} -> (a : A) -> (f : Seq A) -> tail (cons a f) = f
> tailLemma a d = Refl

> consLemma : {A : Type} -> (f : Seq A) -> (n : Nat) -> cons (head f) (tail f) n = f n
> consLemma f    Z  = Refl
> consLemma f (S n) = Refl


* ---------
* Fix point
* ---------

> FixPoint : {X : Type} -> X -> (X -> X) -> Type
> FixPoint x f = x = f x


* ----------------------------
* Sequential decision problems
* ----------------------------

> State  :  Type
> Ctrl   :  (x : State) -> Type
> next   :  (x : State) -> (y : Ctrl x) -> State
> Val    :  Type
> reward :  (x : State) -> (y : Ctrl x) -> State -> Val
> (<+>)  :  Val -> Val -> Val
> LTE    :  Val -> Val -> Type


* --------------------------------------
* Policies and infinite policy sequences
* --------------------------------------

> Policy  :  Type
> Policy  =  (x : State) -> Ctrl x

> PolicySeq  :  Type
> -- PolicySeq  =  Nat -> Policy
> PolicySeq  =  Seq Policy


* ---------------------------------------
* The value of infinite policiy sequences
* ---------------------------------------

The value of making infinite many decision steps with a policy sequence
by starting from a given state is given by a "value" function

> val : PolicySeq -> State -> Val

that fulfils the specification

> valSpec  :  Type
> valSpec  =  (ps : PolicySeq) -> (x : State) -> 
>             val ps x = reward x (head ps x) (next x (head ps x)) 
>             <+> 
>             val (tail ps) (next x (head ps x))

A naive attempt at implementing |val| directly "from its specification"

< val ps x = reward x (head ps x) (next x (head ps x)) <+> val (tail ps) (next x (head ps x))

yiels a possibly non total function. In contrast to SDPs with a finite
number of decision steps, we cannot rely on an induction principle for
decision problems over an infinite number of steps. Obviously, there are
cases in which |val| can be implemented. For instance, if all states
have the same successor. An important case is when |State| is finite. We
discuss this case below.


* ------------------------------
* Optimality of policy sequences
* ------------------------------

> Opt     :  PolicySeq -> Type
> Opt ps  =  (ps' : PolicySeq) -> (x : State) -> val ps' x `LTE` val ps x


* ------------------------
* Optimal policy sequences
* ------------------------

Let |LTE| be a preorder

> reflexiveLTE     :  (a : Val) -> a `LTE` a
> transitiveLTE    :  {a, b, c : Val} -> a `LTE` b -> b `LTE` c -> a `LTE` c

and let |<+>| be monotonous w.r.t. |LTE|

> monotonePlusLTE  :  {a, b, c, d : Val} -> a `LTE` b -> c `LTE` d -> (a <+> c) `LTE` (b <+> d)

We can compute the value of making a first decision step with a given
control and then infinitely many further steps with a given policy
sequence in terms of the (yet to be implemented) |val| function:

> cval         :  (ps : PolicySeq) -> (x : State) -> Ctrl x -> Val
> cval ps x y  =  reward x y (next x y) <+> val ps (next x y)

Assume that, for an arbitrary policy sequence |ps| and for an arbitrary
state |x|, we can pick up a control that maximises |cval ps x|:

> cvalmax         :  (ps : PolicySeq) -> (x : State) -> Val
> cvalargmax      :  (ps : PolicySeq) -> (x : State) -> Ctrl x

> cvalargmaxSpec  :  (ps : PolicySeq) -> (x : State) -> cvalmax ps x = cval ps x (cvalargmax ps x)
> cvalmaxSpec     :  (ps : PolicySeq) -> (x : State) -> (y : Ctrl x) -> cval ps x y `LTE` cvalmax ps x

This is certainly the case if |Ctrl x| is non empty and finite for any
|x| but there are more interesting cases in which we can compute "best"
controls. In these cases, we can compute policies that are optimal
extensions of arbitrary policy sequences:

> OptExt : Policy -> PolicySeq -> Type
> OptExt p ps = (p' : Policy) -> (x : State) -> val (cons p' ps) x `LTE` val (cons p ps) x

> optExt : (ps : PolicySeq) -> Policy
> optExt = cvalargmax

> optExtLemma : (ps : PolicySeq) -> (optExt ps) `OptExt` ps
> optExtLemma ps p' x = s5 where
>   p  : Policy
>   p  = optExt ps
>   s1 : cval ps x (p' x) `LTE` cvalmax ps x
>   s1 = cvalmaxSpec ps x (p' x)
>   s2 : reward x (p' x) (next x (p' x)) <+> val ps (next x (p' x))  `LTE` cvalmax ps x
>   s2 = s1
>   s3 : reward x (p' x) (next x (p' x)) <+> val ps (next x (p' x))  `LTE` cval ps x (p x)
>   s3 = replace {P = \ X => reward x (p' x) (next x (p' x)) <+> val ps (next x (p' x))  `LTE` X} (cvalargmaxSpec ps x) s2
>   s4 : reward x (p' x) (next x (p' x)) <+> val ps (next x (p' x))  `LTE` reward x (p x) (next x (p x)) <+> val ps (next x (p x))
>   s5 : val (cons p' ps) x `LTE` val (cons p ps) x
>   s5 = ?s5prf -- via valSpec, headLemma, tailLemma

This is interesting because of

> Bellman  :  (ps  :  PolicySeq)  ->   Opt ps ->
>             (p   :  Policy)     ->   p `OptExt` ps ->
>             Opt (cons p ps)
> Bellman ps ops p oep = opps where
>   opps : Opt (cons p ps)
>   opps ps' x = s7 where
>     p'   : Policy
>     p'   = head ps'
>     ps'' : PolicySeq
>     ps'' = tail ps'
>     s4   : val (cons p' ps'') x `LTE` val (cons p' ps) x
>     s4   = ?s4prf
>     s5   : val (cons p' ps) x `LTE` val (cons p ps) x
>     s5   = ?s5prf
>     s6   : val (cons p' ps'') x `LTE` val (cons p ps) x
>     s6   = transitiveLTE s4 s5
>     s7   : val ps' x `LTE` val (cons p ps) x
>     s7   = ?s7prf -- via valSpec, consLemma, ... 

I am not sure that this is going to help us but it looks remarkably
similar to the finite horizon case. Perhaps a first step towards
something like

> piter : (Policy, PolicySeq) -> (Policy, PolicySeq)
> piter (p, ps) = (optExt ps, cons (optExt ps) ps)

> piterLemma : (p : Policy) -> (ps : PolicySeq) -> 
>              (p, ps) `FixPoint` piter ->
>              (n : Nat) -> ps n = p
> piterLemma p ps fp  Z    = ( ps Z )
>                          ={ Refl }=
>                            ( head ps )
>                          ={ cong (pairEqElimSnd fp) }=  
>                            ( head (cons (optExt ps) ps) )
>                          ={ headLemma (optExt ps) ps }=  
>                            ( optExt ps )
>                          ={ sym (pairEqElimFst fp) }=
>                            ( p )
>                          QED
> piterLemma p ps fp (S m) = ( ps (S m) )
>                          ={ sym (consLemma ps (S m)) }=
>                            ( cons (head ps) (tail ps) (S m) )
>                          ={ Refl }=
>                            ( (tail ps) m )
>                          ={ replace {P = \ X => (tail ps) m = (tail X) m} (pairEqElimSnd fp) Refl }=
>                            ( (tail (cons (optExt ps) ps)) m )
>                          ={ replace {P = \ X => (tail (cons (optExt ps) ps)) m = (tail (cons X ps)) m} (sym (pairEqElimFst fp)) Refl }=
>                            ( (tail (cons p ps)) m )  
>                          ={ replace {P = \ X => (tail (cons p ps)) m = X m} (tailLemma p ps) Refl }=
>                            ( ps m )
>                          ={ piterLemma p ps fp m }=
>                            ( p )
>                          QED

> Conj : (p : Policy) -> (ps : PolicySeq) -> 
>        (p, ps) `FixPoint` piter ->
>        Opt (cons p ps) 
> Conj p ps fp = opps where
>   opps : Opt (cons p ps)
>   opps = s9 where
>     s0 : (p, ps) = (optExt ps, cons (optExt ps) ps)
>     s0 = fp
>     s1 : p = optExt ps
>     s1 = pairEqElimFst s0
>     s2 : ps = cons (optExt ps) ps
>     s2 = pairEqElimSnd s0
>     s3 : ps = cons p ps
>     s3 = replace {P = \ X => ps = cons X ps} (sym s1) s2
>     s4 : (optExt ps) `OptExt` ps
>     s4 = optExtLemma ps
>     s5 : p `OptExt` ps
>     s5 = replace {P = \ X => X `OptExt` ps} (sym s1) s4
>     s9 : Opt (cons p ps)
>     s9 = Bellman ps ops p oep where
>       ops : Opt ps
>       ops = assert_total (replace {P = \ X => Opt X} (sym s3) s9)
>       oep : p `OptExt` ps
>       oep = s5       


> {-

> ---}



