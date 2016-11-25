> module NoteOnOrderIndependenceAndLocality

> import Syntax.PreorderReasoning
> import Data.List

> %default total
> %auto_implicits off

Assume that we want to apply a function

> A : Type

> f : List A -> List A

to a list of values of type |A|:

> as : List A

Here |A| is a generic type, perhaps representing the state of a cell in
a grid-based computation or the state of an agent in an agent-based
model.  If |as| happens to be very long, one can think of accelerating
the computation of |f as| by splitting |as| into two sublists

> las : List A
> ras : List A
> lasRasSpec : las ++ ras = as

and compute |f las| and |f ras| in parallel. Beside requiring some
technology for parallel computing, this approach requires that |f as|
can be easily computed from |as|, |f las| and |f ras|. Ideally, one
would like to compute |f as| by simply concatenating |f las| and |f
ras|:

> as' : List A
> as' = f las ++ f ras

It is clear that, if |f| is linear w.r.t. concatenation

> Linear : (List A -> List A) -> Type
> Linear f = (xs, ys : List A) -> f xs ++ f ys = f (xs ++ ys)

> fLinear : Linear f

this approach yields the expected result. If we do not feel confident
with our intuition, we can convince ourselves that this is the case (if
you do not feel comfortable with the implementation of |prf|, just skip
to the next paragraph) by computing a value of type |as' = f as|:

> prf : as' = f as
> prf = ( as' )
>     ={ Refl }=
>       ( f las ++ f ras )
>     ={ fLinear las ras }=
>       ( f (las ++ ras) )
>     ={ cong lasRasSpec }=  
>       ( f as )
>     QED

Although we have non-trivial examples of linear |f|s (for instance, |f =
map g| for arbitrary |g : A -> A|), in most practical applications, we
have to deal with functions which are not linear.

Still, the approach outlined above is relevant. Many models in physical
sciences and engineering can be described, in principle, in terms of
"length preserving" functions of type |List A -> List A| for some type
|A|.

These functions are usually not linear and yet the models can be
parallelised efficiently following an approach similar to the one
outlined above.

This approach is sometimes called SPMD: Single Program Multiple Data. In
SPMD approaches for parallel computing, the idea is that a single
program is executed in parallel on multiple "distributed" data.

In the example above, the program was simply |f| and the data were just
the two sublists |las| and |ras|.

In general, the program to be executed in parallel is not just the
original "sequential" program and the distributed data are not simply
chunks of the original data.

Formalizing the problem of implementing a SPMD parallel model of
computation for |f as| would bring us beyond the scope of this note.

But it is important to understand why, in many models in physical
sciences and engineering, SPMD approaches works well. This is
essentially because of two reasons:

1) Order independence
2) Locality 

A computation |f : List A -> List A| is order independent if |f as| is
invariant under permutations of |as|. That is if 

  f as = (inv p) (f (p as))

for any |as| and any permutation |p|. Here |inv p| represents the
inverse permutation of |p|. We can formalize this idea more precisely
(see "Tentative Idris formalization of order independence" below) but
what is important to understand here is why many transition functions at
the core of computational models in physics and engineering are order
independent.

The reason is that, in these models, transitions functions of type |List
A -> List A| are often derived by representing the values of a *finite*
function |t : G -> A| with a list (or array) of values of type |A|.

For instance, |G| could represent the cells of a grid and |t| be a
function that associates a temperature or a number of green cars to the
cells of |G|.

In this context, |as| could represents the average temperatures of the
cells of |G| at a given time and |f as| the temperatures of those cells
cells at a later time. 

In this example, order independence simply reflects the arbitrariness of
the numbering: the results of a computation shall not depend on whether
one chooses to enumerate the grid cells of |G| from top to bottom, left
to right or via a space filling curve!

Order independence is crucial for SPMD approaches towards parallel
computing. In fact, it seems to me (but I have not thought much about
this) that computations that are not order independent are essentially
non-parallelizable.

Thus, it is important to understand whether the transition functions of
a time-stepping model are order independent or not. In the latter case,
it is important to understand whether this is a genuine feature of the
model or a model deficiency.

The second reason why SPMD approaches work well is locality. Informally
|f| is local if every element of |f as| can be computed in terms of a
small (with respect to the length of |as|) number of elements of |as|.

Locality of |f| makes it possible to parallelize the computation of |f
as| by splitting |as| into chunks of size roughly |length as / n| where
|n| is the number of computers at our disposal.


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









 
