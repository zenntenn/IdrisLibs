> import Data.Fin
> import Syntax.PreorderReasoning

> %default total
> %access public export
> %auto_implicits on

> foo :  (n : Nat) -> LTE n m -> Fin (S m)
> foo  Z     LTEZero    = FZ
> foo (S n) (LTESucc p) = FS (foo n p)

> bar : (m : Nat) -> Fin (S m) -> DPair Nat (\ n => LTE n m)
> bar  _     FZ    = (Z ** LTEZero)
> bar  Z    (FS k) = FinZElim k
> bar (S m) (FS k) = (S (fst (bar m k)) ** LTESucc (snd (bar m k)))

> P : Nat -> Nat -> Type
> P n m = LTE n m

> barFooLemma : (m : Nat) -> (n : Nat) -> (p : LTE n m) -> bar m (foo n p) = (n ** p)
> barFooLemma  _     Z     LTEZero    = Refl
> barFooLemma (S m) (S n) (LTESucc p) = 
>     ( bar (S m) (foo (S n) (LTESucc p)) )
>   ={ Refl }=
>     ( bar (S m) (FS (foo n p)) )
>   ={ Refl }=
>     ( (S (fst (bar m (foo n p))) ** LTESucc (snd (bar m (foo n p)))) )
>   ={ ?kuka }= 
>     ( (S (Prelude.Pairs.DPair.fst (the (n : Nat ** P n m) (n ** p))) ** LTESucc (Prelude.Pairs.DPair.snd (the (n : Nat ** P n m) (n ** p)))) )
>   ={ ?kika }=
>     ( (S n ** LTESucc p) )
>   QED


> {-

> depCong1 : {alpha : Type} ->
>            {P : alpha -> Type} ->
>            {a1 : alpha} ->
>            {a2 : alpha} ->
>            {f : (a : alpha) -> P a} ->
>            (a1 = a2) ->
>            f a1 = f a2
> depCong1 Refl = Refl

> barFooLemma : (m : Nat) -> (n : Nat) -> (p : LTE n m) -> bar m (foo n p) = (n ** p)
> barFooLemma  _     Z     LTEZero    = Refl
> barFooLemma (S m) (S n) (LTESucc p) = 
>     ( bar (S m) (foo (S n) (LTESucc p)) )
>   ={ Refl }=
>     ( bar (S m) (FS (foo n p)) )
>   ={ Refl }=
>     ( (S (fst (bar m (foo n p))) ** LTESucc (snd (bar m (foo n p)))) )
>   ={ depCong1 {alpha = DPair Nat (\ i => LTE i m)}
>               {P = \ np => DPair Nat (\ j => LTE j (S m))}
>               {a1 = bar m (foo n p)} 
>               {a2 = (n ** p)} 
>               {f = \ np => (S (fst np) ** LTESucc (snd np))} 
>               (barFooLemma m n p) }=  
>     ( (S (fst (n ** p)) ** LTESucc (snd (n ** p))) )
>   ={ ?kika }=
>     ( (S n ** LTESucc p) )
>   QED

> -}
