> module papers.JFP2016.NaiveMonadicFull

> import papers.JFP2016.NaiveMonadicCore

> import Sigma.Sigma
> import Sigma.Operations

> %default total
> %access public export
> %auto_implicits on


* |M|

> join   :  {A : Type} -> M (M A) -> M A

> MState : (t : Nat) -> Type
> MState t = M (State t)

> mnexts : (t : Nat) -> (mx : MState t) -> (p : ((x : State t) -> Ctrl t x)) -> MState (S t)
> mnexts t mx p = join (fmap (\ x => nexts t x (p x)) mx)


* |LTE|

> reflexiveLTE : (a : Val) -> a `LTE` a
> transitiveLTE : (a : Val) -> (b : Val) -> (c : Val) -> a `LTE` b -> b `LTE` c -> a `LTE` c

> monotonePlusLTE : {a, b, c, d : Val} -> a `LTE` b -> c `LTE` d -> (a `plus` c) `LTE` (b `plus` d)


* |meas|

> measMon  :  {A : Type} ->
>             (f : A -> Val) -> (g : A -> Val) ->
>             ((a : A) -> (f a) `LTE` (g a)) ->
>             (ma : M A) -> meas (fmap f ma) `LTE` meas (fmap g ma)


* |cvalargmax|

> cvalmax  :  (x : State t) -> (ps : PolicySeq (S t) n) -> Val

> cvalargmaxSpec  :  (x  : State t) -> (ps : PolicySeq (S t) n) ->
>                    cvalmax x ps = cval x ps (cvalargmax x ps)

> cvalmaxSpec  :  (x  : State t) -> (ps : PolicySeq (S t) n) ->
>                 (y : Ctrl t x) ->
>                 (cval x ps y) `LTE` (cvalmax x ps)


* The proof of correctness of |backwardsInduction|:

** Policy sequences of length zero are optimal

> nilOptPolicySeq : OptPolicySeq Nil
> nilOptPolicySeq x ps' = reflexiveLTE zero


> {-

> ---}
