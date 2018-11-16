> module Main

> import Syntax.PreorderReasoning
> import Data.List
> import Effects
> import Effect.Exception
> import Effect.StdIO

> %default total
> %access public export
> %auto_implicits off

* 1. An amazingly versatile functional 

They start from the offset with |bigotimes|, the function to be
discussed in the paper

> bigotimes : {X, R : Type} -> List ((X -> R) -> X) -> (List X -> R) -> List X
> bigotimes  Nil      p = Nil
> bigotimes (e :: es) p = x0 :: bigotimes es (p . (x0 ::)) where
>   x0 = e (\ x => p (x :: bigotimes es (p . (x ::))))

, introduce the notion of selection function

> Selection : Type -> Type -> Type 
> Selection X R = (X -> R) -> X

and of a "binary operation that combines two selection functions" in
terms of which |bigotimes| can be implemented recursively. In the rest
of the section they relate |bigotimes| with sequential games (apparently
deterministic, with finite or infinite number of steps and alternating
players), with the Tychonoff theorem and with the Double-Negation Shift
(DNS). Then they present an outline of the paper.


* 2. Selection functions

They start by introducing shortcuts for (flipped) selection functions

> J : Type -> Type -> Type
> J R X = (X -> R) -> X

and generalized quantifiers 

> K : Type -> Type -> Type
> K R X = (X -> R) -> R

Here, |R| represents generalized truth values. The text suggests that
selection functions of type |J R X| and quantifiers of type |K R X| take
as arguments functions of type |X -> R| that represent properties of
values of type |X|, see the "Terminology" table.

As a matter of fact, however, these functions are not dependently
typed. I think that the arguments of selection functions and quantifiers
are in fact decision procedured associated for a decidable property of
interest. Thus, for instance, for |X = Nat| and |R = Bool|, one could
have

> P : Nat -> Type
> P i = LTE i 42

and

> dP : Nat -> Bool
> dP i = if i <= 42 then True else False

Anyway, the authors go on by remarking that, with the |J| operator, the
type of |bigotimes| can be rewritten as

< bigotimes : {X, R : Type} -> List (J R X) -> J R (List X)

They then introduce

> overline : {X, R : Type} -> J R X -> K R X
> overline e = \ p => p (e p)

and start discussing selection functions for sets in a subsection. 


** 2.1 Selection functions for sets 

Escardo-Oliva start by stating that "A selection function for a set S
finds an element of S for which a given predicate holds". They require
selection functions for sets to be total and point out that "if there is
no element of S satisfying the predicate, we select an arbitrary element
of S". Thus, selection functions for sets are only defined for non-empty
sets

> find : {X : Type} -> (xs : List X) -> NonEmpty xs -> J Bool X -- J Bool xs
> find      Nil  _ p impossible
> find (x :: xs) _ p with (nonEmpty xs)
>   | (Yes prf) = if p x then x else find xs prf p
>   | ( No prf) = x

> forsome : {X : Type} -> (xs : List X) -> NonEmpty xs -> K Bool X
> forsome xs ne = overline (find xs ne)

> forevery : {X : Type} -> (xs : List X) -> NonEmpty xs -> K Bool X
> forevery xs ne p = not (forsome xs ne (not . p))

At this point, Escardo-Oliva point out that their definition of the
existential quantifier is the same as in Hilbert’s ε-calculus: 

  ∃x p(x) ⇐⇒ p(ε(p)).

This looks like a claim about |find|:

> findLemma1 : {X : Type} -> 
>              (xs : List X) -> (ne : NonEmpty xs) -> (p : X -> Bool) -> 
>              (x ** p x = True) -> p (find xs ne p) = True

> findLemma2 : {X : Type} -> 
>              (xs : List X) -> (ne : NonEmpty xs) -> (p : X -> Bool) -> 
>              p (find xs ne p) = True -> (x ** p x = True)

The second lemma holds trivially

> findLemma2 {X} xs ne p prf = (find xs ne p ** prf) 

and it should not be difficult to show that the first one holds as well
using the implementation of |find|:

> findLemma2 {X}      Nil  _ p prf impossible
> findLemma2 {X} (x :: xs) _ p prf = ?lala

Further, they state that a selection function ε for a set S has to
satisfy:

1. ε(p) ∈ S, whether or not there actually is some x ∈ S such that p(x)
   holds.

2. If p(x) holds for some x ∈ S, then it holds for x = ε(p).

With the helper function

> typeOf : {X : Type} -> X -> Type
> typeOf {X} _ = X 

the first condition boils down to

> SpecJ1 : {X, R : Type} -> (eps : J R X) -> (p : X -> R) -> typeOf (eps p) = X

which trivially holds

> SpecJ1 eps p = Refl

In the second condition it is not completely clear what it means for
p(x) to "hold". If we restrict ourselves to the case in which |R =
Bool|, I think that the condition could be written as

< SpecJ2 : {X : Type} -> (eps : J Bool X) -> (p : X -> Bool) -> (x : X) -> p x = True -> p (eps p) = True  

Here we have translated "p(x) holds" with |p x = True|. If the arguments
of selection functions and quantifiers were truly propositions, we would
again know how to formalize condition 2

< SpecJ2 : {X : Type} -> (eps : J Type X) -> (p : X -> Type) -> (x : X) -> p x -> p (eps p)


** 2.2 Selection functions for quantifiers

Hilbert's condition

  ϕ p = p (ε p)

is used to express what it means for a selection function to be
compatible with a quantifier:

> infixl 9 <> 

> (<>) : {X, R : Type} -> (eps : J R X) -> (phi : K R X) -> Type
> (<>) {X} {R} eps phi = (p : X -> R) -> phi p = p (eps p)  

This trivially implies

> overlineLemma : {X, R : Type} -> (eps : J R X) -> eps <> overline eps
> overlineLemma eps = \ p => Refl

Then they give examples of selection functions that are compatible with
given quantifiers. One for the universal quantifier

< forevery : {X : Type} -> (xs : List X) -> NonEmpty xs -> K Bool X
< forevery xs ne p = not (forsome xs ne (not . p))

is |findnot|:

> findnot : {X : Type} -> (xs : List X) -> NonEmpty xs -> J Bool X
> findnot      Nil  _ p impossible
> findnot (x :: xs) _ p with (nonEmpty xs)
>   | (Yes prf) = if p x then find xs prf p else x
>   | ( No prf) = x

they argue. They first notice that

> findnotLemma : {X : Type} -> 
>                (xs : List X) -> (ne : NonEmpty xs) ->
>                (p : X -> Bool) -> findnot xs ne p = find xs ne (not . p)

and 

> foreveryFindnotLemma : {X : Type} -> 
>                        (xs : List X) -> (ne : NonEmpty xs) -> 
>                        (p : X -> Bool) -> 
>                        forevery xs ne p = overline (findnot xs ne) p

from which they conclude

> findnotForeveryLemma : {X : Type} -> 
>                        (xs : List X) -> (ne : NonEmpty xs) -> 
>                        findnot xs ne <> forevery xs ne
> findnotForeveryLemma xs ne p = ( forevery xs ne p )
>                              ={ foreveryFindnotLemma xs ne p }=
>                                ( overline (findnot xs ne) p )
>                              ={ overlineLemma (findnot xs ne) p }=
>                                ( p (findnot xs ne p) )
>                              QED

Further examples of selection functions are given for "predicates" that
return numbers rather than Boolean values:

> {-

> argsup : {X : Type} -> (xs : List X) -> (ne : NonEmpty xs) -> J Int X
> argsup      Nil  _ p impossible
> argsup (x :: xs) _ p with (nonEmpty xs)
>   | (Yes prf) = if p x < p x' then x' else x 
>       where x' = argsup xs prf p
>   | ( No prf) = x

> arginf : {X : Type} -> (xs : List X) -> (ne : NonEmpty xs) -> J Int X
> arginf xs ne p = argsup xs ne (\ x => - p x)

>-}

-- > partial
-- > argsup : {X : Type} -> List X -> J Int X  --  here Int is just {-1, 0, 1}
-- > -- argsup [] p  =  undefined
-- > argsup {X} (x :: xs) p  =  f xs x (p x)
-- >   where
-- >   f : List X -> X -> Int -> X
-- >   f xs' a 1  =  a
-- >   f [] a r  =  a
-- >   f xs'       a  0    =  g xs'
-- >     where
-- >     g []  =  a
-- >     g (a :: as)  = if  p a  ==  1  then  a else g as
-- >   f (x' :: xs') a r  =  f xs' x' (p x') -- at this point, r = -1
                 
-- > {- original implementation (non-optimised) -}
-- > partial
-- > argsup : {X : Type} -> (xs : List X) -> J Int X
-- > argsup (x :: xs) p with (nonEmpty xs)
-- >   | (Yes prf) = if p x < p x' then x' else x 
-- >       where x' = argsup xs p
-- >   | ( No prf) = x

> partial
> argsup : {X : Type} -> (xs : List X) -> J Int X
> argsup (x :: Nil) p = x
> argsup (x :: x' :: xs) p = if p x < p x' then argsup (x' :: xs) p else argsup (x :: xs) p


-- > findnot xs prf p  =  find xs prf (not . p)


> partial
> arginf : {X : Type} -> (xs : List X) -> J Int X
> arginf xs p = argsup xs (\ x => - p x)


* 3 Products of selection functions

** 3.1 Binary product

> opairJ : {X, Y, R : Type} -> J R X -> J R Y -> J R (X,Y)
> opairJ epsx epsy p = (a, b) where
>   a = epsx (\ x => overline epsy (\ y => p (x, y)))
>   b = epsy (\ y => p (a, y))

> opairK : {X, Y, R : Type} -> K R X -> K R Y -> K R (X,Y)
> opairK phix phiy p = phix (\ x => phiy (\ y => p (x, y)))

It is easy to see that |opairJ| implements two backwards induction steps
followed by a forward computation of "optimal" controls:

> opairJ' : {X, Y, R : Type} -> J R X -> J R Y -> J R (X,Y)
> opairJ' {X} {Y} epsx epsy p = (x, y) where
>   piy  :  X -> Y
>   piy  =  \ x => epsy (\ y => p (x, y))
>   pix  :  Unit -> X
>   pix  =  \ u => epsx (\ x => p (x, piy x))
>   x    :  X
>   x    =  pix ()
>   y    :  Y
>   y    =  piy x

In this context, the set of states at decision steps one and two are
|Unit| and |X|, respectively. The controls are |X| in the first step and
|Y| in the second step.

In order to compute the result of |opairJ' epsx epsy p|, we first
compute |piy|. This is an optimal policy for the second (last) step in
the sense that for every |x : X|, |piy x| is a "best" control, that is

< p (x, piy x) = overline epsy (curry p x)

< p (x, piy x)
<
<   { Def. |piy| } 
<
< p (x, epsy (\ y => p (x, y)))
<
<   { Def. |curry| }
<
< (curry p) x (epsy (\ y => curry p x y))
<
<   { Abstraction }
<
< (curry p) x (epsy (curry p x))
<
<   { |overline e q = q (e q)| with |q = (curry p) x| and |e = epsy| }
<
< overline epsy (curry p x)

Then, we compute |pix|. This is an optimal extension of |piy| in the
sense that for every |u : Unit|, |pix u| is a "best" control *under the
assumption that the next decision is taken with |piy|*, that is

< p (pix u, piy (pix u)) = overline epsx (\ x => curry p x (piy x))

< p (pix u, piy (pix u))
<
<   { Def. |pix| }
<
< p (epsx (\ x => p (x, piy x)), piy (epsx (\ x => p (x, piy x))))
<
<   { Def. |curry| }
<
< (curry p) (epsx (\ x => p (x, piy x))) (piy (epsx (\ x => p (x, piy x))))
<
<   { Let |g = \ x => p (x, piy x)| }
<
< (curry p) (epsx g) (piy (epsx g))
<
<   { |overline e q = q (e q)| with |q = (curry p) x| and |e = epsy| }


|optPP| takes two selection functions for values of arbitrary types |X|
and |Y| and a predicate on |(X,Y)|. It returns a pair of functions. The
first function associates a control |x : X| to every value of type
|Unit|. Here |Unit| is the set of possible states at the first decision
step. The second function associates a control |y : Y| to every state in
|X|. At the second decision step, |X| and |Y| represent the state and
the control sets, respectively. We can easily implement |opairJ| in
terms of |optPP|:


** 3.2 Iterated product

Define the product of a "sequence of sets |X 0|, |X 1|, ..., |X n|,
...". First we need a tail function for families of types:

> Tail : (Nat -> Type) -> (Nat -> Type)
> Tail X = \ n => X (S n) 

Then we can define the product as a list

> data Prod : (Nat -> Type) -> Type where
>   Nil   :  {X : Nat -> Type} -> Prod X
>   (::)  :  {X : Nat -> Type} -> (x : X Z) -> Prod (Tail X) -> Prod X

We cannot implement the iterated product in terms of |opairJ| because
the types of the arguments have to be in the relation implied by
|Prod|. We need a more specific helper:

> oprodJ : {X : Nat -> Type} -> {R : Type} ->
>          J R (X Z) -> J R (Prod (Tail X)) -> J R (Prod X)  
> oprodJ e ep p = a :: as where
>   a  = e (\ x => overline ep (\ xs => p (x :: xs)))
>   as = ep (\ xs => p (a :: xs))

With |oprodJ| implementing the iterated product is easy: 

> bigoprodJ : {X : Nat -> Type} -> {R : Type} ->
>             Prod ((J R) . X) -> J R (Prod X)
> bigoprodJ      Nil  = \ p => Nil
> bigoprodJ (e :: es) = oprodJ e (bigoprodJ es)

We can do othe same with vectors instead of lists 

< data Prod : Nat -> (Nat -> Type) -> Type where
<   Nil   :               {X : Nat -> Type} -> Prod Z X
<   (::)  :  {n : Nat} -> {X : Nat -> Type} -> (x : X Z) -> Prod n (Tail X) -> Prod (S n) X

< oprodJ : {X : Nat -> Type} -> {R : Type} -> {n : Nat} ->
<          J R (X Z) -> J R (Prod n (Tail X)) -> J R (Prod (S n) X)  
< oprodJ e ep p = a :: as where
<   a  = e (\ x => overline ep (\ xs => p (x :: xs)))
<   as = ep (\ xs => p (a :: xs))

< bigoprodJ : {X : Nat -> Type} -> {R : Type} -> {n : Nat} -> 
<             Prod n ((J R) . X) -> J R (Prod n X)
< bigoprodJ      Nil  = \ p => Nil
< bigoprodJ (e :: es) = oprodJ e (bigoprodJ es)

Because they do not have dependent types, they implement |bigoprodJ| in
Haskell for the special case of a constant family of types:

> otimesJ : {X : Type} -> {R : Type} ->
>           J R X -> J R (List X) -> J R (List X)  
> otimesJ e ep p = a :: as where
>   a  = e (\ x => overline ep (\ xs => p (x :: xs)))
>   as = ep (\ xs => p (a :: xs))

> bigotimesJ : {X, R : Type} -> List (J R X) -> J R (List X)
> bigotimesJ      Nil  = \ p => Nil
> bigotimesJ (e :: es) = otimesJ e (bigotimesJ es)


* 4. Playing games

** 4.2 History dependent games

-- > hotimesJ : {X : Type} -> {R : Type} ->
-- >           J R X -> (X -> J R (List X)) -> J R (List X)  
-- > hotimesJ e f p = a :: as where
-- >   a  = e (\ x => overline (f x) (\ xs => p (x :: xs)))
-- >   as = (f a) (\ xs => p (a :: xs))

> hotimesJ : {X : Type} -> {R : Type} ->
>           J R X -> (X -> J R (List X)) -> J R (List X)  
> hotimesJ e0 e1 p = a0 :: a1
>   where
>   a0 = e0 (\ x0 => overline (e1 x0) (\ x1 => p (x0 :: x1)))
>   a1 = e1 a0 (\ x1 => p (a0 :: x1))

> bighotimesJ : {X, R : Type} -> List (List X -> J R X) -> J R (List X)
> bighotimesJ [] = \p => []
> bighotimesJ (e :: es)  =  (e []) `hotimesJ` (\x => bighotimesJ [\ xs => d (x :: xs) | d <- es])


** 4.3 Implementation of games and optimal strategies


-- > data Game : Type -> Type -> Type where
-- >   MkGame : {Move, Outcome : Type} -> 
-- >            (p : List Move -> Outcome) -> 
-- >            (es : List (List Move -> J Outcome Move)) -> 
-- >            Game Move Outcome

-- > pred : {Move, Outcome : Type} -> Game Move Outcome -> (List Move -> Outcome)
-- > pred (MkGame p _) = p

-- > epss : {Move, Outcome : Type} -> Game Move Outcome -> List (List Move -> J Outcome Move)
-- > epss (MkGame _ es) = es


> {-
> optimalStrategy : {Move, Outcome : Type} -> Game Move Outcome -> List Move -> Move
> optimalStrategy {Move} {Outcome} g ms = head (optimalPlay g') where
>   g' : Game Move Outcome
>   g' = MkGame p' es' where
>     p'   :  List Move -> Outcome
>     p'   =  \ ms' => (pred g) (ms ++ ms') 
>     es'  :  List (List Move -> J Outcome Move)
>     es'  =  drop (length ms) (epss g)
> -}


** 4.5 Tic-Tac-Toe

> data Player =  X | O

> Outcome : Type
> Outcome = Int

> Move : Type
> Move = Int

> Board : Type
> Board = (List Move, List Move)





> someContained : {X : Type} -> Ord X => 
>                 List (List X) -> List X -> Bool


> wins : List Move -> Bool
> wins = someContained [[0,1,2],[3,4,5],[6,7,8],
>                       [0,3,6],[1,4,7],[2,5,8],
>                       [0,4,8],[2,4,6]]

> value : Board -> Outcome
> value (xs, os) = if wins xs 
>                  then 1
>                  else if wins os 
>                       then -1
>                       else 0

> insert : {X : Type} -> Ord X => X -> List X -> List X

> outcome : Player -> List Move -> Board -> Board
> outcome _      Nil     board = board
> outcome X (m :: ms) (xs, os) = if wins os 
>                                then (xs, os)
>                                else outcome O ms (insert m xs, os)
> outcome O (m :: ms) (xs, os) = if wins xs 
>                                then (xs, os)
>                                else outcome X ms (xs, insert m os)


> setMinus : {X : Type} -> Ord X => 
>            List X -> List X -> List X

-- > partial 
-- > es : List (List Move -> J Outcome Move)
-- > es = take 3 all where
-- >   partial
-- >   eX  :  List Move -> J Outcome Move
-- >   eX  =  \ h => argsup (setMinus [0..8] h)
-- >   partial
-- >   eO  :  List Move -> J Outcome Move
-- >   eO  =  \ h => arginf (setMinus [0..8] h)
-- >   partial
-- >   all :  List (List Move -> J Outcome Move)
-- >   all =  [eX, eO, eX, eO, eX, eO, eX, eO, eX, eO]

-- > partial
-- > ticTacToe : Game Move Outcome
-- > ticTacToe = MkGame p es


> partial 
> epsilons : List (List Move -> J Outcome Move)
> epsilons = take 3 all where
>   partial
>   eX  :  List Move -> J Outcome Move
>   eX  =  \ h => argsup (setMinus [0..8] h)
>   partial
>   eO  :  List Move -> J Outcome Move
>   eO  =  \ h => arginf (setMinus [0..8] h)
>   partial
>   all :  List (List Move -> J Outcome Move)
>   all =  [eX, eO, eX, eO, eX, eO, eX, eO, eX, eO]

> p : List Move -> Outcome
> p ms = value (outcome X ms (Nil, Nil))

> partial
> optimalPlay : List Move
> optimalPlay = bighotimesJ epsilons p

> partial
> optimalOutcome : Outcome
> optimalOutcome = p optimalPlay



> partial
> main : IO ()
> main = 
>   do putStr ("An optimal play for Tic-Tac-Toe is "
>              ++
>              show optimalPlay ++ "\n"
>              ++
>              "and the optimal outcome is "
>              ++
>              show optimalOutcome ++ "\n"
>              )


** 4.7 Appendix

> contained : {X : Type} -> Ord X => List X -> List X -> Bool
> contained       []        ys  = True
> contained       xs        []  = False
> contained (x :: xs) (y :: ys) = if x == y 
>                                 then contained xs ys
>                                 else if x >= y
>                                      then contained (x :: xs) ys
>                                      else False

> someContained         []  ys  = False
> someContained        xss  []  = False
> someContained (xs :: xss) ys = contained xs ys || someContained xss ys

> insert x [] = [x]
> insert x (y :: ys) = if x == y 
>                      then (y :: ys)
>                      else if x < y
>                           then x :: (y :: ys)
>                           else y :: (insert x ys) 

> delete : {X : Type} -> Ord X => X -> List X -> List X
> delete x [] = []
> delete x (y :: ys) = if x == y
>                      then ys
>                      else if x < y
>                           then y :: ys
>                           else y :: Main.delete x ys

> setMinus xs       []  = xs
> setMinus xs (y :: ys) = setMinus (Main.delete y xs) ys

> {-

 
> ---}


 
 
