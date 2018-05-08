> %default total
> %auto_implicits off

> X : Type
> H : Type
> fulfils : X -> H -> Bool

> LTE : H -> H -> Type
> LTE h1 h2 = (x : X) -> fulfils x h1 = True -> fulfils x h2 = True

> antisymmetricLTE : (h1 : H) -> (h2 : H) -> h1 `LTE` h2 -> h2 `LTE` h1 -> 
>                    (x : X) -> fulfils x h1 = fulfils x h2 
> antisymmetricLTE h1 h2 p q y with (fulfils y h1)
>   | True  = ?kika
>   | False = ?kiko
