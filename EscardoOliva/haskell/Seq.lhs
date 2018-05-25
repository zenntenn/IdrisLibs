< bigotimes :: [(x -> r) -> x] -> ([x] -> r) -> [x]
< bigotimes  []        p  =  []
< bigotimes  (e : es)  p  =  x0 : bigotimes es (p . (x0:))
<   where
<            x0           =  e (\ x -> p (x : bigotimes es (p . (x:))))

* Selection functions

> type J r x  =  (x -> r) -> x  -- intuition: Hilbert's epsilon

< bigotimes  ::  [J r x] -> J r [x]

> type K r x  =  (x -> r) -> r  -- intuition: quantifier

> overline   ::  J r x -> K r x
> overline e  =  \ p -> p (e p)

** Selection functions for sets

> find :: [x] -> J Bool x 
> find []  p       =  undefined
> find [x] p       =  x
> find (x : xs) p  =  if p x then x else find xs p

> forsome, forevery  ::  [x] -> K Bool x
> forsome        =  overline . find
> forevery xs p  =  not (forsome xs (not . p))

> findbool  ::  J Bool Bool
> findbool p  =  p True

** Selection function for quantifiers

For phi(p) = \E x (p x), we have

  phi(p) = p (epsilon (p))  <=>  phi = overline epsilon

Generalise: epsilon is a selection function for quantifier phi if phi = overline epsilon

Example: universal quantifier

  forall = overline epsilonF
<=>
  forall p = p (epsilonF p)

What can epsilonF be?

We have

  forall p = not (exists (not . p)) = not ((not.p) (epsilon (not.p))) = p (epsilon (not . p))

Therefore

  epsilonF = \ p -> epsilon (not . p) -- epsilon . not

> findnot :: [x] -> J Bool x
> findnot xs p  =  find xs (not . p)

Generalise to J Int, e.g., J Int Bool

> argsupB :: J Int Bool
> argsupB p  =  p True > p False

> supB :: K Int Bool
> supB  =  overline argsupB

> argsupL :: [x] -> J Int x
> argsupL [] p  =  undefined
> argsupL [x] p  =  x
> argsupL (x : x' : xs) p  =  if p x > p x' then argsup (x : xs) p else argsup (x' : xs) p

> argsup :: [x] -> J Int x  --  here Int is just {-1, 0, 1}
> argsup [] p  =  undefined
> argsup (x : xs) p  =  f xs x (p x)
>   where
>   f xs a 1  =  a
>   f [] a r  =  a
>   f (x : xs) a (-1)  =  f xs x (p x)
>   f xs       a  0    =  g xs
>     where
>     g []  =  a
>     g (x : xs)  |  p x  ==  1   =  x
>                 |  otherwise    =  g xs

> arginf :: [x] -> J Int x
> arginf xs p = argsup xs (\ x -> - p x)

* Products of selection functions

** Binary product

> epsprod :: J r x0 -> J r x1 -> J r (x0, x1)
> epsprod eps0 eps1 p = (x0', x1') where
>   x0' = eps0 (\ x0 -> p (x0, eps1 (\ x1 -> p (x0, x1))))
>   x1' = eps1 (\ x1 -> p (x0', x1))
>

My claim: (x0', x1') = epsprod eps0 eps1 p => x0' = eps0 (\ x -> p (x, x1'))

This would be Belmann's principle! (x1' is the result of an epsilon)

Exercise:

> qprod :: K r x0 -> K r x1 -> K r (x0, x1)
> qprod q0 q1 p = q0 (\ x0 -> q1 (\ x1 -> p (x0, x1)))

Exercise:

  qprod (overline eps0) (overline eps1) = overline (epsprod eps0 eps1)

** Iterated product

Using lists instead of tuples, e.g.

> epsprod' :: J r x -> J r [x] -> J r [x]
> epsprod' eps0 eps1 p = x0' : x1s' where
>   x0' = eps0 (\ x0 -> p (x0 : eps1 (\ x1s -> p (x0 : x1s))))
>   x1s' = eps1 (\ x1s -> p (x0' : x1s))

> itprod  :: [J r x] -> J r [x]
> itprod [] p             =  []
> itprod (eps : epses) p  =  epsprod' eps (itprod epses) p

* Playing Games

** Optimal outcomes, plays and strategies

Remark: in general, X_{i+1} will depend on X_i

Remark: "... and False if Abelard has a winning strategy"
        Actually, it's stronger: False if Eloise does not have a winning strategy.


> otimes :: J r x -> (x -> J r [x]) -> J r [x]
> otimes e0 e1 p = a0 : a1
>   where
>   a0 = e0(\x0 -> overline (e1 x0)(\x1 -> p (x0 : x1)))
>   a1 = e1 a0 (\x1 -> p (a0 : x1))

> bigotimes :: [[x] -> J r x] -> J r [x]
> bigotimes [] = \p -> []
> bigotimes (e : es)  =  e [] `otimes` (\x -> bigotimes [\xs -> d (x : xs) | d <- es])

> data Player = X | O

> type R = Int

> type Move = Int

> type Board = ([Move], [Move])

> wins :: [Move] -> Bool
> wins = someContained [[0,1,2],[3,4,5],[6,7,8], [0,3,6],[1,4,7],[2,5,8], [0,4,8],[2,4,6]]


> value :: Board -> R
> value (x,o) | wins x = 1
>             | wins o = -1
>             | otherwise = 0


> outcome :: Player -> [Move] -> Board -> Board
> outcome whoever [] board = board
> outcome X (m : ms) (x, o) = if wins o then (x, o) else outcome O ms (insert m x, o)
> outcome O (m : ms) (x, o) = if wins x then (x, o) else outcome X ms (x, insert m o)

> p :: [Move] -> R
> p ms = value(outcome X ms ([],[]))

> epsilons :: [[Move] -> J R Move]
> epsilons = take 9 all
>   where
>   all = epsilonX : epsilonO : all
>   epsilonX h = argsup ([0..8] `setMinus` h)
>   epsilonO h = arginf ([0..8] `setMinus` h)

> main :: IO ()
> main = putStr ("An optimal play for Tic-Tac-Toe is " ++ show optimalPlay ++
>        "\nand the optimal outcome is " ++ show optimalOutcome ++ "\n")


> optimalPlay :: [Move]
> optimalPlay = bigotimes epsilons p

> optimalOutcome :: R
> optimalOutcome = p optimalPlay



> contained :: Ord x => [x] -> [x] -> Bool
> contained [] ys = True
> contained xs [] = False
> contained (us@(x : xs)) (y : ys) | x == y = contained xs ys
>                                  | x >= y = contained us ys
>                                  | otherwise = False

> someContained :: Ord x => [[x]] -> [x] -> Bool
> someContained [] ys = False
> someContained xss [] = False
> someContained (xs : xss) ys = contained xs ys || someContained xss ys

> insert :: Ord x => x -> [x] -> [x]
> insert x [] = [x]
> insert x (vs@(y : ys)) | x == y = vs
>                        | x < y = x : vs
>                        | otherwise = y : insert x ys

> delete :: Ord x => x -> [x] -> [x]
> delete x [] = []
> delete x (vs@(y : ys)) | x == y = ys
>                        | x < y = vs
>                        | otherwise = y : delete x ys

> setMinus :: Ord x => [x] -> [x] -> [x]
> setMinus xs [] = xs
> setMinus xs (y : ys) = setMinus (delete y xs) ys

