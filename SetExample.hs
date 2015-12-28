-- vim: ts=2: sw=2: expandtab: ai:

import MicroKanren
import ExampleMember

import Control.Applicative
import Control.Monad



-- set example

ex1 = fresh $ \x-> S[x,x,x,x,x] `eq` S [x]
ex2 = fresh $ \(x,y) -> S[x] `eq` S [x,y]
ex3 = fresh $ \(x,y) -> S[x,x] `eq` S [x,y]
ex4 = fresh $ \(x,y) -> S[x,x,x] `eq` S [x,y]
ex5 = fresh $ \(x,y) -> S[x,x,y,x,x] `eq` S [x,y]
ex6 = fresh $ \(x,y) -> S[x,x,y,x,x] `eq` S [x,y,y,y]
ex7 = fresh $ \(x,y) -> S[x,x,y,x,x] `eq` S [x,y,y,y,x,x]

ex8 = fresh $ \(x,y) -> do{S [y,x] `eq` S [x,y]}

ex9 = fresh $ \x -> S [x] `eq` x
ex9'= fresh $ \x -> x `eq` S [x]

ex10 = fresh $ \x -> S[S [x]] `eq` S [x]
ex10'= fresh $ \x -> S [x] `eq` S[S [x]]



-- list to set

list2set l s = fresh $ \(a,l',s') -> 
  do{ l `eq` cons a l'; list2set l' s'; S as <- expand s'; s `eq` S(a:as) }
  <|>
  do{ l `eq` nil; s `eq` S[] }


(tm0,st0) = head $ test $ fresh $ \(l,s) -> list2set (cons (A"a") l) s >> expand' s

dotst = tst $ fresh $ \(l,s) -> list2set (cons (A"a") l) s >> expand' s
