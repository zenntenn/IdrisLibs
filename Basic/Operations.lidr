> module Basic.Operations


> %default total

> %access public export


* Extensions of |replace|, |cong|

> |||
> replace2 : {a : _} -> {a1 : _} -> {a2 : _} ->
>            {b : _} -> {b1 : _} -> {b2 : _} ->
>            {P : a -> b -> Type} ->
>            (a1 = a2) -> (b1 = b2) -> P a1 b1 -> P a2 b2
> replace2 Refl Refl p = p

> |||
> cong2 : {alpha : Type} ->
>         {beta : Type} ->
>         {gamma : Type} ->
>         {a1 : alpha} ->
>         {a2 : alpha} ->
>         {b1 : beta} ->
>         {b2 : beta} ->
>         {f : alpha -> beta -> gamma} ->
>         (a1 = a2) ->
>         (b1 = b2) ->
>         f a1 b1 = f a2 b2
> cong2 Refl Refl = Refl

> |||
> depCong1 : {alpha : Type} ->
>            {P : alpha -> Type} ->
>            {a1 : alpha} ->
>            {a2 : alpha} ->
>            {f : (a : alpha) -> P a} ->
>            (a1 = a2) ->
>            f a1 = f a2
> depCong1 Refl = Refl

> |||
> depCong2 : {alpha : Type} ->
>            {P : alpha -> Type} ->
>            {gamma : Type} ->
>            {a1 : alpha} ->
>            {a2 : alpha} ->
>            {Pa1 : P a1} ->
>            {Pa2 : P a2} ->
>            {f : (a : alpha) -> P a -> gamma} ->
>            (a1 = a2) ->
>            (Pa1 = Pa2) ->
>            f a1 Pa1 = f a2 Pa2
> depCong2 Refl Refl = Refl

> |||
> depCong2' : {alpha : Type} ->
>             {P : alpha -> Type} ->
>             {Q : (a : alpha) -> P a -> Type} ->
>             {a1 : alpha} ->
>             {a2 : alpha} ->
>             {Pa1 : P a1} ->
>             {Pa2 : P a2} ->
>             {f : (a : alpha) -> (pa : P a) -> Q a pa} ->
>             (a1 = a2) ->
>             (Pa1 = Pa2) ->
>             f a1 Pa1 = f a2 Pa2
> depCong2' Refl Refl = Refl
