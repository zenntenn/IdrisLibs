> module SimpleProb.Measures

> import SimpleProb.SimpleProb
> import SimpleProb.BasicOperations
> import NonNegRational.NonNegRational
> import NonNegRational.BasicOperations
> import NonNegRational.BasicProperties

> %default total
> %access public export
> %auto_implicits off


* Measures

> ||| Expected value
> expectedValue : SimpleProb NonNegRational -> NonNegRational
> expectedValue = Prelude.Foldable.sum . (map (uncurry (*))) . toList


