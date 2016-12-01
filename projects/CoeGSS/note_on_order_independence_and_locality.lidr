> module NoteOnOrderIndependenceAndLocality

> import Syntax.PreorderReasoning
> import Data.List

> %default total
> %auto_implicits off


* Model parallelization

When we talk about "parallelizing a model" in the context of agent-based
modelling, computational economics, climate modelling, etc. we mean
deriving model implementations that can be executed efficiently on a
parallel computer.

In this context, being parallel (in contrast to sequential) is a
property of model implementations, not of model specifications.

Often, a sequential implementation of a model is used as a blueprint for
deriving parallel implementations. But it is also possible to derive
parallel model implementations directly from model specifications.

What takes place "in parallel" (instead of sequentially) in a parallel
model implementation are certain computations.

During a simulation (execution of a model implementation), some level of
parallelism is almost always automatically enforced by the underlying
computing architecture. Thus, for instance, in every modern CPU, reading
data from memory and performing certain arithmetic operations can be
done in parallel. A compiler can, up to a certain extent, reorganize the
details of a computation to exploit this parallelism.

When we talk of parallelism in the context of "parallelizing a model" we
do not mean this level of parallelism. Instead, we mean a much coarser
level of parallelism in which the computational cost of a simulation is
distributed on, say, |n| CPUs (possibly each with its own memory) with
the explicit goal of reducing the simulation time by a factor |n|.

In this context, we say that a parallel implementation of a model can be
executed efficiently on a certain parallel computer if, for small values
of |n| and on that computer, doubling |n| roughly cuts the time it takes
to run a simulation by two.

A rather counter-intuitive fact of parallel computing is that doubling
the number of CPUs sometimes allows running a simulation in
significantly less than half the time. 

In the jargon, this effect is sometimes referred to as "super-linear
speedup". Super-linear speedup can be easily explained in terms of
memory-efficiency. I mention it here just in case you have heard about
it and thought that someone was trying to fool you.


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









 
