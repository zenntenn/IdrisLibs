> module CoinductiveCalculus.CoinductiveCalculus

> import Syntax.PreorderReasoning

> %default total
> %access public export
> %auto_implicits off

> %hide Stream
> %hide head
> %hide tail
> %hide (+)
> %hide plusZeroRightNeutral

* Streams

For a type |T|, streams of values of type |T| can be described by values
of type |Stream T| with

> Stream : Type -> Type

The idea is that any |Stream T| has a head and a tail

> head : {T : Type} -> Stream T -> T
> tail : {T : Type} -> Stream T -> Stream T

and that piecing together a |T| with a |Stream T| obtains another
|Stream T|:

> cons : {T : Type} -> T -> Stream T -> Stream T

The stream operations |head|, |tail| and |cons| are required to fulfil
three properties:

> headConsProp : {T : Type} -> (t : T) -> (s : Stream T) -> head (cons t s) = t  

> tailConsProp : {T : Type} -> (t : T) -> (s : Stream T) -> tail (cons t s) = s

> consHeadTailProp : {T : Type} -> (s : Stream T) -> cons (head s) (tail s) = s 


* Differentiation and integration

We want to look at differentiation and integration of functions of real
variables from the point of view of streams. More specifically, we want
to understand which properties differentiation and integration have to
fulfill when we look at differentiation and integration as operations on
streams of type |Stream R = F|. Here

> R : Type

is taken to represent real numbers and

> F : Type
> F = R -> R

are differentiable and integrable functions on |R|:

> D : F -> F

> S : R -> R -> F -> R

How can we implement |head| for |Stream R = F|? We have

> headF : F -> R

The obvioius way to compute a real number from a |f : F| is to evaluate
|f|. Thus, we require our "real numbers" to contain at least one
element, say zero:

> zero : R

and we define

> headF f = f zero

What about the tail of a function |f|?

> tailF : F -> F

The only operation that we can apply on values of type |F| that
obviously matches the type of |tailF| is |D|. Thus

> tailF = D

We are left with the implementation of |cons| for real numbers and
functions on real numbers:

> consF : R -> F -> F

Of course, we want |headF|, |tailF| and |consF| to fulfill the
properties of stream operations. In particular, we want

< consF (headF f) (tailF f) = f

For |f = consF a g| and our definitions of |headF| and |tailF|, this is
equivalent to

< consF (headF f) (tailF f) = f
<
<   ={ def. of f }=
<
< consF (headF (consF a g)) (tailF (consF a g)) = consF a g
<
<   ={ def. of consF, tailF }=
<
< consF ((consF a g) zero) (D (consF a g)) = consF a g

Sufficient conditions for the last equality to hold are

< (consF a g) zero = a 

and 

< D (consF a g) = g

The first condition can be fulfiled by defining |consF a g| to be |const
a|. The second condition requires |consF a g| has to be the
anti-derivative of |g|. This suggests the definition

> (+) : R -> R -> R

> consF a f = \ x => a + S zero x f


* Properties of |R|, |D| and |S|

Which properties do |R|, |D| and |S| have to satisfy for |headF|,
|tailF| and |consF| to be stream operations? Our definition already
require |R| to be equipped with a zero element and with a |(+)| binary
operation:

< R : Type
< zero : R
< (+) : R -> R -> R

If we also require integration to fulfill

> intProp1 : (a : R) -> (f : F) -> S a a f = zero

and |zero| to be a

> plusZeroRightNeutral : (left : R) -> left + zero = left 

We can derive a formal proof of |headF (consF a f) = a|:

> headConsPropF : (a : R) -> (f : F) -> headF (consF a f) = a  
> headConsPropF a f = ( headF (consF a f) )
>                   ={ Refl }=
>                     ( headF (\ x => a + S zero x f) )
>                   ={ Refl }=
>                     ( a + S zero zero f )
>                   ={ cong (intProp1 zero f) }=  
>                     ( a + zero )
>                   ={ plusZeroRightNeutral a }=
>                     ( a )
>                   QED

Similarly, if we assume that the derivative of constant functions is zero

> derConstZero : (a : R) -> D (const a) = const zero

, that |D| is linear

> derLinear1 : (f, g : F) -> D (\ x => f x + g x) = \ x => (D f) x + (D g) x

, that integration is an "anti-derivative"

> intAntiDer : (f : F) -> D (\ x => S zero x f) = f

, that |zero| is a

> plusZeroLeftNeutral : (right : R) -> zero + right = right 

we can derive a formal proof of |tailF (consF a f) = f|. For this, however,
we also need extensional equality on |F|:

> extEqF : (f, g : F) -> ((x : R) -> f x = g x) -> f = g

With these assumptions one has

> lemma : (f : F) -> (x : R) -> zero + f x = f x
> lemma f x = ( zero + f x )
>           ={ plusZeroLeftNeutral (f x) }=
>             ( f x )
>           QED

> tailConsPropF : (a : R) -> (f : F) -> tailF (consF a f) = f  
> tailConsPropF a f = ( tailF (consF a f) )
>                   ={ Refl }=
>                     ( tailF (\ x => a + S zero x f) )
>                   ={ Refl }=
>                     ( D (\ x => a + S zero x f) ) 
>                   ={ Refl }=
>                     ( D (\ x => (const a) x + (\ y => S zero y f) x) )  
>                   ={ derLinear1 (const a) (\ y => S zero y f) }=
>                     ( \ x => (D (const a)) x + (D (\ y => S zero y f)) x ) 
>                   ={ cong {f = \ h => \ x => h x + (D (\ y => S zero y f)) x } (derConstZero a) }=
>                     ( \ x => (const zero) x + (D (\ y => S zero y f)) x )
>                   ={ cong {f = \ h => \ x => (const zero) x + h x} (intAntiDer f) }=
>                     ( \ x => (const zero) x + f x )
>                   ={ Refl }=
>                     ( \ x => zero + f x )
>                   ={ extEqF (\ x => zero + f x) (\ x => f x) (lemma f) }=
>                     ( \ x => f x )
>                   ={ Refl }=  
>                     ( f )
>                   QED




> {-

> ---}
 
