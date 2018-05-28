> module EscardoOliva.TestSelectionFunction

> import EscardoOliva.SelectionFunction

> %default total
> %access public export
> %auto_implicits off


> xs : List Int
> xs = [0,3,2,-1,0,9,-7]

> min : Int
> min = arginf xs id

> max : Int
> max = argsup xs id
