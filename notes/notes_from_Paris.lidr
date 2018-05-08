> module NotesFromParis -- meeting with Antoine in Paris, Friday 20 Apr. 2018

> import Syntax.PreorderReasoning
> import Data.List

> import Finite.Predicates

> %default total
> %auto_implicits off


* Agents and opinions

We have a set of agents

> Agent : Type

and a set of opinions

> Opinion : Type

The set of agents is finite

> fAgent : Finite Agent

and every agent has certain neighbors

> neighbors : Agent -> List Agent

and an opinion

> opinion : Agent -> Opinion


* Opinion dynamics

Agents sequentially update their opinions according to the opinions of
their neighbors. In the context of the fixed neighborhood relation
provided by |neighbors|, the updating rule has type

< update : (Agent -> Opinion) -> (Agent -> Opinion)

We can be a little bit more general and let

> M : Type -> Type

account for uncertainties in the way agents update their opinions:

> update : (Agent -> Opinion) -> M (Agent -> Opinion)

The idea, originally put forward in [1], is that |M| is a monad. Thus,
it has, among others, an associated

> mapM : {A, B : Type} -> (A -> B) -> M A -> M B 

that preserves identity and composition. We do not insist on a full
specification of |M| here but see [2].


* Games of influence

In a game of influence, a (typically small) number of players try to
influence the dynamics of opinions by modifying the opinion of a
specific agent at each step of a sequence of opinion updates

> modify : (Eq Agent) => 
>          (Agent, Opinion) -> (Agent -> Opinion) -> (Agent -> Opinion)
> modify (a, o) ops = ops' where
>   ops' : Agent -> Opinion
>   ops' x = if x == a then o else ops x

The requirement |Eq Agent| underlines the fact that the implementation
of |modify| relies on equality between agents to be decidable. This is a
natural requirement, especially since |Agent| is finite. 

For the sake of simplicity, let's consider the case of two players. 

Given the choices of the two players, a modify-and-update
single step of a game of influence can described in two ways

> step : (Eq Agent) => 
>        (Agent, Opinion) -> (Agent, Opinion) -> (Agent -> Opinion) -> M (Agent -> Opinion)
> step ao1 ao2 = update . (modify ao2) . (modify ao1) 

or

< step : (Eq Agent) => 
<        (Agent, Opinion) -> (Agent, Opinion) -> (Agent -> Opinion) -> M (Agent -> Opinion)
< step ao1 ao2 = update . (modify ao1) . (modify ao2) 

The interpretation is obvious: for any "current" opinion distribution |x
: Agent -> Opinion| and choices |ao1 : (Agent, Opinion)| |ao2 : (Agent,
Opinion)| of the two players, |step ao1 ao2 x| is an |M|-structure (a
list or a probability distribution) of "next" opinion distributions.

Notice that, in general, the two implementations of |step| are not
equivalent if the two players select the same agent but different
opinions.

The idea of a game of influence is that, upon selection an agent-opinion
pair and performing an single modify-and-update step, each player
receives a reward of an arbitrary type |Val|:

> Val : Type

Typically, rewards are natural numbers (or perhaps a real numbers) and
may depend on the current opinion of the agents, on the agent-opinion
pairs chosen by the players and on the opinions obtained in a single
step:

> reward : (Eq Agent) => 
>          (Agent -> Opinion) -> 
>          (Agent, Opinion) -> 
>          (Agent, Opinion) -> 
>          (Agent -> Opinion) -> (Val, Val)

The interpretation of |reward| follows from the interpretation of
|step|: for any opinion distribution |x : Agent -> Opinion| and choices
|ao1 : (Agent, Opinion)| |ao2 : (Agent, Opinion)| of the two players,
|mapM (reward x ao1 ao2) (step ao1 ao2 x) : M (Val, Val)| are the
"possible" rewards of the players. We can encode this interpretation in
a |rewards| function:

> rewards : (Eq Agent) => 
>           (Agent -> Opinion) -> 
>           (Agent, Opinion) -> 
>           (Agent, Opinion) -> 
>           M (Val, Val)
> rewards x ao1 ao2 = mapM (reward x ao1 ao2) (step ao1 ao2 x)

The goal of the players is to select agent-opinion pairs that maximize a
sum of the rewards obtained over a whole game. This can consist of a
finite or of an infinite number of steps.


* Infinite horizon games of influence

Remember that |Agent| is finite. Typically, 


* References

[1] Ionescu, C. (2009). Vulnerability Modelling and Monadic Dynamical
    Systems change. Freie Universitaet Berlin,
    https://d-nb.info/1023491036/34.

[2] Botta, N., Jansson, P. & Ionescu, C. (2017). Contributions to a
    computational theory of policy advice and avoidability. J. Funct.
    Program., 27, e23.


> {-

* Parallel computations on lists (arrays, etc.)

Assume that, for a given type |A|

> A : Type

we want to apply a function

> f : List A -> List A

to a list of values of type |A|:

> as : List A

Here |A| could represent, for instance, values associated to the nodes
or to the cells of a grid in a model for numerical weather
forecasting. Or |A| could represent the state of an agent in an
agent-based model. If |f as| happens to be computationally expensive
(perhaps because |as| is very long), one can think of accelerating the
computation of |f as| by splitting |as| into two sublists

> las : List A
> ras : List A
> lasRasSpec : las ++ ras = as

and computing |f las| and |f ras| in parallel. Beside requiring some
infrastructure for parallel computations, this approach requires that |f
as| can be computed from |as|, |f las| and |f ras| at a computational
cost which is negligible with respect to the cost of computing |f as|
directly. Ideally, one would like to compute |f as| by simply
concatenating |f las| and |f ras|:

> as' : List A
> as' = f las ++ f ras

If |f| happens to be linear w.r.t. concatenation

> Linear : (List A -> List A) -> Type
> Linear f = (xs, ys : List A) -> f xs ++ f ys = f (xs ++ ys)

> fLinear : Linear f

|as'| obviously yields the expected result. If we do not feel confident
with our intuition, we can convince ourselves that this is the case by
proving that |as' = f as|. This can be done in Idris easily (if you do
not feel comfortable with the following implementation of |prf|, just
skip to the next paragraph):

> prf : as' = f as
> prf = ( as' )
>     ={ Refl }=
>       ( f las ++ f ras )
>     ={ fLinear las ras }=
>       ( f (las ++ ras) )
>     ={ cong lasRasSpec }=  
>       ( f as )
>     QED


* Order-independent, stencil-based functions, SPMD approaches

Although we have non-trivial examples of linear functions (for instance,
|f = map g| for arbitrary |g : A -> A|), in many model implementations,
we have to deal with functions which are not linear. 

As it turns out, the simple-minded approach outlined above can often be
extended to cope with functions which are not linear if these happen to
be

1) Order independent
2) Stencil-based.

There are examples of computations that are not order independent and
yet can be easily parallelized. For instance, in sorting algorithms.

But for model implementations which heavily rely on functions of type
|List A -> List A| which are not order independent and stencil-based,
parallelizability is, to say the least, questionable. Thus, for
instance, many agent-based models of exchange economies are essentially
non-parallelizable.

Luckily, many sequential implementations of models in physical sciences
and engineering can be described in terms of length preserving functions
of type |List A -> List A| which fulfil 1) and 2).

These implementations can be parallelized (relatively) easily and
efficiently following a SPMD approach. SPMD means Single Program
Multiple Data. In SPMD approaches for parallel computing, a single
program is executed in parallel on multiple "distributed" data.

In the example above, such program was simply |f| and the data were the
two sublists |las| and |ras|.

For non-linear functions which are order independent and stencil-based,
the program to be executed in parallel is not just the original
"sequential" program and the distributed data are not simply chunks of
the original data.

Formalizing the problem of implementing a SPMD-parallel equivalent of |f
as| would bring us beyond the scope of this note.

But it is important to understand what it means for |f : List A -> List
A| to be order independent and stencil-based and why many models in
physical sciences and engineering are implemented in terms of transition
functions that fulfill these properties.


* Order independence

A computation |f : List A -> List A| is order independent if |f as| is
invariant under permutations of |as|. That is if

  f as = (inv p) (f (p as))

for any |as| and any permutation |p|. Here |inv p| represents *the*
inverse permutation of |p|. We can formalize this idea more precisely,
see "Tentative Idris formalization of order independence" below. 

But, before getting there, let me try to explain why the transition
functions of many sequential implementations of computational models in
physics and engineering are order independent.

The reason is simple: in these implementations, transitions functions of
type |List A -> List A| are usually derived by representing *finite*
function of type |G -> A| in terms of lists (arrays, tables, etc.)  of
values of type |A|.

The idea is that, if |G| is finite, one can number the elements of
|G|. For instance, if |G| represent the cells of a grid and |t : G -> A|
is a function that associates a temperature or a number of green cars to
the grid cells, one can represent |t| with a list of real numbers or
with a list of natural numbers by selecting a particular order for
visiting the grid cells.

Thus, while a model might be specified in terms of transitions functions
of type |(G -> A) -> (G -> A)|, model implementations are often written
in terms of transition functions of type |List A -> List A|.

In these cases, order independence simply reflects the arbitrariness of
the numbering used to represent finite functions: the results of a
computation shall not depend on whether the grid cells are enumerated
from top to bottom, left to right, or by means of a space filling curve!

Order independence is crucial for parallelizing sequential model
implementations following a SPMD approach.

Thus, for understanding whether a sequential implementation of a model
can be "SPMD parallelized" easily, it is important to understand whether
its transition functions are order independent or not.

In the second case, it is important to understand whether the lack of
order independence is just a feature of the particular sequential
implementation or a genuine feature of the model's transition function.


* Stencil-basedness

If order independent computations of type |List A -> List A| are
stencil-based, they can be parallelized efficiently via SPMD
approaches. Informally |f| is stencil-based if every element of |f as|
can be computed in terms of a small (with respect to the length of |as|)
number of elements of |as|.

Stencil-basedness (locality) of |f| makes it possible to parallelize the
computation of |f as| by splitting |as| into chunks of size roughly
|length as / n| where |n| is the number of computers at our disposal.


* Tentative Idris formalization of order independence

We say that |p : List A -> List A| is a permutation iff for all |as :
List A|, |p as| computes a list of the same length of |as| which
contains all the elements of |as|:

> Permutation : (List A -> List A) -> Type
> Permutation p = (as : List A) -> ( length (p as) = length as, 
>                                    (a : A) -> a `Elem` as -> a `Elem` (p as) )

We say that, for any types |X|, |Y| and any bijective function |f : X ->
Y|, |inv f| is an inverse of |f| if it is a left and a right inverse

> Injective : {X, Y : Type} -> (f : X -> Y) -> Type
> Injective {X} f = (a1 : X) -> (a2 : X) -> f a1 = f a2 -> a1 = a2

> Surjective : {X, Y : Type} -> (f : X -> Y) -> Type
> Surjective {Y} f = (b : Y) -> Exists (\ a => f a = b)

> Bijective : {X, Y : Type} -> (f : X -> Y) -> Type
> Bijective f = (Injective f, Surjective f)

> inv : {X, Y : Type} -> (X -> Y) -> (Y -> X)
> invLI : {X, Y : Type} -> (f : X -> Y) -> Bijective f -> (inv f) . f = id 
> invRI : {X, Y : Type} -> (f : X -> Y) -> Bijective f -> f . (inv f) = id 

With these notions in place, we can explain what it means for a function
|f : List A -> List A| to be order independent:

> OrderIndependent : (List A -> List A) -> Type
> OrderIndependent f = (as : List A) -> 
>                      (p : List A -> List A) -> 
>                      Permutation p -> 
>                      f as = (inv p) (f (p as)) 

> ---}







 
