> module Nat.examples.InductiveProofs
 
> import Syntax.PreorderReasoning

> succPlusLeftRightEqPlusLeftSuccRight : (m : Nat) -> (n : Nat) -> S (plus m n) = plus m (S n)
> succPlusLeftRightEqPlusLeftSuccRight  Z    n = Refl
> succPlusLeftRightEqPlusLeftSuccRight (S m) n = ( S (plus (S m) n) )
>                                              ={ Refl }=
>                                                ( S (S (plus m n)) )
>                                              ={ cong (succPlusLeftRightEqPlusLeftSuccRight m n) }=
>                                                ( S (plus m (S n)) )
>                                              ={ Refl }=
>                                                ( plus (S m) (S n) )
>                                              QED

