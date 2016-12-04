> module Fraction.LTEProperties

> import Syntax.PreorderReasoning

> import Fraction.Fraction
> import Fraction.BasicOperations
> import Fraction.Predicates
> import Fraction.BasicProperties
> import PNat.PNat
> import PNat.Operations
> import PNat.Properties
> import Nat.LTEProperties
> import Nat.LTProperties
> import Nat.OperationsProperties
> import Nat.Positive

> %default total
> %access export
> -- %access public export

> -- %freeze PNatOperations.toNat

|LTE| is a total preorder:

> ||| LTE is reflexive
> reflexiveLTE : (x : Fraction) -> x `LTE` x
> reflexiveLTE (n, d') = Nat.LTEProperties.reflexiveLTE (n * (toNat d'))


> ||| LTE is transitive
> transitiveLTE : (x, y, z : Fraction) -> x `LTE` y -> y `LTE` z -> x `LTE` z
> transitiveLTE (nx, dx') (ny, dy') (nz, dz') xLTEy yLTEz = s8 where
>   dx : Nat
>   dx = toNat dx'
>   dy : Nat
>   dy = toNat dy'
>   dz : Nat
>   dz = toNat dz'
>   s1    : LTE ((nx * dy) * dz) ((ny * dx) * dz)
>   s1    = monotoneNatMultLTE xLTEy (Nat.LTEProperties.reflexiveLTE dz)
>   s2    : LTE ((ny * dz) * dx) ((nz * dy) * dx)
>   s2    = monotoneNatMultLTE yLTEz (Nat.LTEProperties.reflexiveLTE dx)
>   s3    : LTE ((ny * dx) * dz) ((nz * dy) * dx)
>   s3    = replace {P = \ ZUZ => LTE ZUZ ((nz * dy) * dx)} (multSwapRight ny dz dx) s2
>   s4    : LTE ((nx * dy) * dz) ((nz * dy) * dx)
>   s4    = Nat.LTEProperties.transitiveLTE ((nx * dy) * dz)
>                                           ((ny * dx) * dz)
>                                           ((nz * dy) * dx)
>                                           s1 s3
>   s5    : LTE ((nx * dz) * dy) ((nz * dy) * dx)
>   s5    = replace {P = \ ZUZ => LTE ZUZ ((nz * dy) * dx)} (multSwapRight nx dy dz) s4
>   s6    : LTE ((nx * dz) * dy) ((nz * dx) * dy)
>   s6    = replace {P = \ ZUZ => LTE ((nx * dz) * dy) ZUZ} (multSwapRight nz dy dx) s5
>   s7    : LTE (nx * dz) (nz * dx)
>   s7    = elimRightMultLTE {a = nx * dz} {b = nz * dx} {c = dy} {d = dy}
>                            s6 Refl (gtZisnotZ (denLTLemma (ny, dy')))
>   s8 : (nx, dx') `LTE` (nz, dz')
>   s8 = s7

                        
> ||| LTE is total
> totalLTE : (x, y : Fraction) -> Either (x `LTE` y) (y `LTE` x) 
> totalLTE (n1, d1') (n2, d2') = 
>   let d1 = toNat d1' in
>   let d2 = toNat d2' in
>   Nat.LTEProperties.totalLTE (n1 * d2) (n2 * d1)


Properties of |LTE| and |plus|:

> ||| LTE is monotone w.r.t. `plus`
> monotonePlusLTE : {a, b, c, d : Fraction} -> 
>                   a `LTE` b -> c `LTE` d -> (a `plus` c) `LTE` (b `plus` d)
> monotonePlusLTE {a = (na, da')} {b = (nb, db')} {c = (nc, dc')} {d = (nd, dd')} aLTEb cLTEd = s16 where
>   da : Nat
>   da = toNat da'
>   db : Nat
>   db = toNat db'
>   dc : Nat
>   dc = toNat dc'
>   dd : Nat
>   dd = toNat dd'
>   s1 : LTE (na * db) (nb * da)
>   s1 = aLTEb
>   s2 : LTE (nc * dd) (nd * dc)
>   s2 = cLTEd
>   s3 : LTE ((na * db) * (dc * dd)) ((nb * da) * (dc * dd))
>   s3 = monotoneNatMultLTE s1 (Nat.LTEProperties.reflexiveLTE (dc * dd))
>   s4 : LTE ((nc * dd) * (da * db)) ((nd * dc) * (da * db))
>   s4 = monotoneNatMultLTE s2 (Nat.LTEProperties.reflexiveLTE (da * db))
>   s5 : LTE ((na * db) * (dc * dd) + (nc * dd) * (da * db)) 
>            ((nb * da) * (dc * dd) + (nd * dc) * (da * db))
>   s5 = monotoneNatPlusLTE s3 s4 
>   s6 : LTE ((na * dc) * (db * dd) + (nc * dd) * (da * db)) 
>            ((nb * da) * (dc * dd) + (nd * dc) * (da * db))
>   s6 = replace {P = \ ZUZ => LTE (         ZUZ          + (nc * dd) * (da * db)) 
>                                  ((nb * da) * (dc * dd) + (nd * dc) * (da * db))} 
>                (multSwap23 na db dc dd) s5 
>   s7 : LTE ((na * dc) * (db * dd) + (nc * da) * (dd * db)) 
>            ((nb * da) * (dc * dd) + (nd * dc) * (da * db))
>   s7 = replace {P = \ ZUZ => LTE ((na * dc) * (db * dd) +          ZUZ         ) 
>                                  ((nb * da) * (dc * dd) + (nd * dc) * (da * db))} 
>                (multSwap23 nc dd da db) s6
>   s8 : LTE ((na * dc) * (db * dd) + (nc * da) * (dd * db)) 
>            ((nb * dd) * (dc * da) + (nd * dc) * (da * db))
>   s8 = replace {P = \ ZUZ => LTE ((na * dc) * (db * dd) + (nc * da) * (dd * db)) 
>                                  (         ZUZ          + (nd * dc) * (da * db))} 
>                (multSwap24 nb da dc dd) s7
>   s9 : LTE ((na * dc) * (db * dd) + (nc * da) * (dd * db)) 
>            ((nb * dd) * (dc * da) + (nd * db) * (da * dc))
>   s9 = replace {P = \ ZUZ => LTE ((na * dc) * (db * dd) + (nc * da) * (dd * db)) 
>                                  ((nb * dd) * (dc * da) +          ZUZ         )} 
>                (multSwap24 nd dc da db) s8                
>   s10 : LTE ((na * dc) * (db * dd) + (nc * da) * (db * dd)) 
>             ((nb * dd) * (dc * da) + (nd * db) * (da * dc))
>   s10 = replace {P = \ ZUZ => LTE ((na * dc) * (db * dd) + (nc * da) *    ZUZ   ) 
>                                   ((nb * dd) * (dc * da) + (nd * db) * (da * dc))} 
>                 (multCommutative dd db) s9
>   s11 : LTE ((na * dc) * (db * dd) + (nc * da) * (db * dd)) 
>             ((nb * dd) * (da * dc) + (nd * db) * (da * dc))
>   s11 = replace {P = \ ZUZ => LTE ((na * dc) * (db * dd) + (nc * da) * (db * dd)) 
>                                   ((nb * dd) *    ZUZ    + (nd * db) * (da * dc))} 
>                 (multCommutative dc da) s10
>   s12 : LTE ((na * dc + nc * da) * (db * dd)) 
>             ((nb * dd) * (da * dc) + (nd * db) * (da * dc))
>   s12 = replace {P = \ ZUZ => LTE ZUZ ((nb * dd) * (da * dc) + (nd * db) * (da * dc))} 
>                 (sym (multDistributesOverPlusLeft (na * dc) (nc * da) (db * dd))) s11
>   s13 : LTE ((na * dc + nc * da) * (db * dd)) ((nb * dd + nd * db) * (da * dc))
>   s13 = replace {P = \ ZUZ => LTE (((na * dc) + (nc * da)) * (db * dd)) ZUZ} 
>                 (sym (multDistributesOverPlusLeft (nb * dd) (nd * db) (da * dc))) s12
>   s14 : LTE ((na * dc + nc * da) * (toNat (db' * dd'))) ((nb * dd + nd * db) * (da * dc))
>   s14 = replace {P = \ ZUZ => LTE ((na * dc + nc * da) * ZUZ) ((nb * dd + nd * db) * (da * dc))} 
>                 (sym toNatMultLemma) s13
>   s15 : LTE ((na * dc + nc * da) * (toNat (db' * dd'))) ((nb * dd + nd * db) * (toNat (da' * dc')))
>   s15 = replace {P = \ ZUZ => LTE ((na * dc + nc * da) * (toNat (db' * dd'))) ((nb * dd + nd * db) * ZUZ)}
>                 (sym toNatMultLemma) s14
>   s16 : ((na, da') `plus` (nc, dc')) `LTE` ((nb, db') `plus` (nd, dd'))
>   s16 = s15


Properties of |LTE| and |mult|:

> ||| LTE is monotone w.r.t. `(*)`
> monotoneMultLTE : {a, b, c, d : Fraction} -> 
>                   a `LTE` b -> c `LTE` d -> (a `mult` c) `LTE` (b `mult` d)
> monotoneMultLTE {a = (na, da')} {b = (nb, db')} {c = (nc, dc')} {d = (nd, dd')} aLTEb cLTEd = s13 where
>   da : Nat
>   da = toNat da'
>   db : Nat
>   db = toNat db'
>   dc : Nat
>   dc = toNat dc'
>   dd : Nat
>   dd = toNat dd'
>   s01 : LTE (na * db) (nb * da)
>   s01 = aLTEb
>   s02 : LTE (nc * dd) (nd * dc)
>   s02 = cLTEd
>   s03 : LTE ((na * db) * (nc * dd)) ((nb * da) * (nc * dd))
>   s03 = monotoneNatMultLTE s01 (Nat.LTEProperties.reflexiveLTE (nc * dd))
>   s04 : LTE ((nc * dd) * (da * nb)) ((nd * dc) * (da * nb))
>   s04 = monotoneNatMultLTE s02 (Nat.LTEProperties.reflexiveLTE (da * nb))
>   s05 : LTE ((da * nb) * (nc * dd)) ((nd * dc) * (da * nb))
>   s05 = replace {P = \ ZUZ => LTE ZUZ ((nd * dc) * (da * nb))} 
>                 (multCommutative (nc * dd) (da * nb)) s04
>   s06 : LTE ((nb * da) * (nc * dd)) ((nd * dc) * (da * nb))
>   s06 = replace {P = \ ZUZ => LTE (ZUZ * (nc * dd)) ((nd * dc) * (da * nb))} 
>                 (multCommutative da nb) s05
>   s07 : LTE ((na * db) * (nc * dd)) ((nd * dc) * (da * nb))
>   s07 = Nat.LTEProperties.transitiveLTE ((na * db) * (nc * dd)) ((nb * da) * (nc * dd)) ((nd * dc) * (da * nb)) s03 s06
>   s08 : LTE ((na * nc) * (db * dd)) ((nd * dc) * (da * nb))
>   s08 = replace {P = \ ZUZ => LTE ZUZ ((nd * dc) * (da * nb))} 
>                 (multSwap23 na db nc dd) s07
>   s09 : LTE ((na * nc) * (db * dd)) ((nd * nb) * (da * dc))
>   s09 = replace {P = \ ZUZ => LTE ((na * nc) * (db * dd)) ZUZ} 
>                 (multSwap24 nd dc da nb) s08
>   s10 : LTE ((na * nc) * (db * dd)) ((nb * nd) * (da * dc))
>   s10 = replace {P = \ ZUZ => LTE ((na * nc) * (db * dd)) (ZUZ * (da * dc))} 
>                 (multCommutative nd nb) s09
>   s11 : LTE ((na * nc) * (toNat (db' * dd'))) ((nb * nd) * (da * dc))
>   s11 = replace {P = \ ZUZ => LTE ((na * nc) * ZUZ) ((nb * nd) * (da * dc))} 
>                 (sym toNatMultLemma) s10
>   s12 : LTE ((na * nc) * (toNat (db' * dd'))) ((nb * nd) * (toNat (da' * dc')))
>   s12 = replace {P = \ ZUZ => LTE ((na * nc) * (toNat (db' * dd'))) ((nb * nd) * ZUZ)}
>                 (sym toNatMultLemma) s11
>   s13 : ((na, da') `mult` (nc, dc')) `LTE` ((nb, db') `mult` (nd, dd'))
>   s13 = s12


