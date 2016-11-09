> module Nat.open_issues.Main

> %default total
> %auto_implicits off

> n : Nat
> -- n = 80

> -- %freeze n

> ns : List Nat
> ns = [1..n]

> postulate lemma : (m : Nat) -> 2 * (sum [1..m]) = m * (S m)

> q : 2 * (sum ns) = n * (S n)
> q = lemma n

> {-
> main : IO ()
> main = do putStrLn ("n           = " ++ show n)
>           putStrLn ("sum ns      = " ++ show (sum ns))
> -}

For small |n|, type checking time is roughly constant in |n| and
execution time is roughly linear in |n| as one would expect: 

    n   | type check |  run
  ======|============|======= 
  10000 |       5.7s | 0.006s
  20000 |       5.8s | 0.012s
  40000 |       6.0s | 0.028s
  80000 |       5.8s | 0.060s

But uncommenting the computation of |q| yields unacceptable type
checking times even for very small |n|:

    n   | type check |  run
  ======|============|======= 
   10   |       6.0s | 0.002s
   20   |       5.7s | 0.002s
   40   |       7.6s | 0.002s
   80   |      29.7s | 0.002s
  160   |   11m55.0s | 0.002s
  320   |  243m22.0s | 0.002s
  640   |   killed!  | 



