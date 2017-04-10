> module InfiniteHorizonSequentialDecisionProblems.Theory

> %default total
> %access public export
> %auto_implicits off


* Sequential decision processes

> State  :  Type
> Ctrl   :  (x : State) -> Type
> M      :  Type -> Type
> nexts  :  (x : State) -> (y : Ctrl x) -> M State
> fmap   :  {A, B : Type} -> (A -> B) -> M A -> M B


* Sequential decision problems

> Val              :  Type
> reward           :  (x : State) -> (y : Ctrl x) -> (x' : State) -> Val
> plus             :  Val -> Val -> Val
> LTE              :  Val -> Val -> Type
> meas             :  M Val -> Val


* Policies

> Policy  :  Type
> Policy  =  (x : State) -> Ctrl x


* The value of policies

> ||| A value function ...
> val : State -> Policy -> Val

> ||| ... that fulfils the specification
> valSpec  :  Type
> valSpec  =  (x : State) -> (p : Policy) -> 
>             val x p 
>             = 
>             meas (fmap (\ x' => reward x (p x) x' `plus` val x' p) (nexts x (p x)))


* Optimality of policies

> |||
> Opt    :  Policy -> Type
> Opt p  =  (x : State) -> (p' : Policy) -> val x p' `LTE` val x p


* Optimal policies

> ||| 
> cval        :  (x : State) -> Ctrl x -> (p : Policy) -> Val
> cval x y p  =  meas (fmap (\ x' => reward x y x' `plus` val x' p) (nexts x y))

> cvalargmax      :  (x : State) -> (p : Policy) -> Ctrl x

> ||| A policy ...
> opt : Policy

> ||| ... that fulfils Bellman's equation
> optSpec  :  Type
> optSpec  =  (x : State) -> opt x = cvalargmax x opt  


* Optimality of |opt|

** Additional assumptions

> reflexiveLTE     :  (a : Val) -> a `LTE` a
> transitiveLTE    :  {a, b, c : Val} -> a `LTE` b -> b `LTE` c -> a `LTE` c
> monotonePlusLTE  :  {a, b, c, d : Val} -> a `LTE` b -> c `LTE` d -> (a `plus` c) `LTE` (b `plus` d)
> measMon          :  {A : Type} ->
>                     (f : A -> Val) -> (g : A -> Val) ->
>                     ((a : A) -> (f a) `LTE` (g a)) ->
>                     (ma : M A) -> meas (fmap f ma) `LTE` meas (fmap g ma)

> cvalmax         :  (x : State) -> (p : Policy) -> Val
> cvalargmaxSpec  :  (x : State) -> (p : Policy) -> cvalmax x p = cval x (cvalargmax x p) p
> cvalmaxSpec     :  (x : State) -> (y : Ctrl x) -> (p : Policy) -> (cval x y p) `LTE` (cvalmax x p)


** |opt| is optimal

> mutual

>   ||| ... is an optimal policy
>   optLemma1  :  (vs : valSpec) -> (os : optSpec) ->
>                 (x : State) -> (y : Ctrl x) -> (p : Policy) -> 
>                 cval x y p `LTE` cval x y opt
>   optLemma1 vs os x y p = s9 where
>     f' : State -> Val
>     f' = \ x' => reward x y x' `plus` val x' p 
>     f  : State -> Val
>     f  = \ x' => reward x y x' `plus` val x' opt
>     s1 : (x' : State) -> val x' p `LTE` val x' opt
>     s1 x' = assert_total (optLemma2 vs os) x' p
>     s2 : (x' : State) -> (f' x') `LTE` (f x')
>     s2 x' = monotonePlusLTE (reflexiveLTE (reward x y x')) (s1 x')
>     s3 : meas (fmap f' (nexts x y)) `LTE` meas (fmap f (nexts x y))
>     s3 = measMon f' f s2 (nexts x y)
>     s9 : cval x y p `LTE` cval x y opt
>     s9 = s3

>   ||| ... is an optimal policy
>   optLemma2 : (vs : valSpec) -> (os : optSpec) -> Opt opt
>   optLemma2 vs os x p' = s9 where
>     s1 : val x p' = cval x (p' x) p'
>     s1 = vs x p'
>     s2 : cval x (p' x) p' `LTE` cval x (p' x) opt
>     s2 = assert_total optLemma1 vs os x (p' x) p'
>     s3 : cval x (p' x) opt `LTE` cvalmax x opt
>     s3 = cvalmaxSpec x (p' x) opt
>     s4 : cvalmax x opt = cval x (cvalargmax x opt) opt
>     s4 = cvalargmaxSpec x opt
>     s5 : cval x (cvalargmax x opt) opt = cval x (opt x) opt
>     s5 = replace {P = \ U => cval x U opt = cval x (opt x) opt} (os x) Refl
>     s6 : cval x (opt x) opt = val x opt
>     s6 = sym (vs x opt)
>     s7 : cval x (p' x) p' `LTE` cvalmax x opt
>     s7 = transitiveLTE s2 s3
>     s8 : val x p' `LTE` cvalmax x opt
>     s8 = replace {P = \ W => W `LTE` cvalmax x opt} (sym s1) s7
>     s9 : val x p' `LTE` val x opt
>     s9 = replace {P = \ W => val x p' `LTE` W} (trans (trans s4 s5) s6) s8


> {-


> ---}


