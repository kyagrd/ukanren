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
  do{ l `eq` nil; s `eq` S[] }
  <|>
  do{ l `eq` cons a l'; list2set l' s'; S as <- expand s'; s `eq` S(a:as) }

(tm0,st0) = head $ test $ fresh $ \(l,s) -> list2set (cons (A"a") l) s >> expand' s

dotst = tst $ fresh $ \(l,s) -> list2set (cons (A"a") l) s >> expand' s

-- list generator
list l = l `eq` nil <|> (fresh $ \(x,xs) -> do { l `eq` cons x xs; list xs })

-- subset on native set values using list generator
subset s1 s2 = do
  s1e <- expand s1
  s2e <- expand s2
  case (s1e, s2e) of
    (S [],  _  ) -> ok
    (S xs, S ys) -> conjs [disjs [x `eq` y | y <- usort ys] | x <- usort xs]
    (V _ , S ys) -> disjs [s1e `eq` S xs | xs <- subsets (usort ys)]
    (S xs, V _ ) -> fresh $ \(l,s) ->
                      do { list l; list2set l s
                         ; s' <- expand s
                         ; case s' of S ys -> s2e `eq` S(usort $ xs++ys)
                                      _    -> mzero
                         }
    (V _ , V _ ) -> fresh $ \(xs,ys) ->
                      do { list xs ; list2set xs s1e
                         ; list ys ; list2set ys s2e
                         ; subset s1e s2e
                         }
    _ -> fail $ "cannot subset" ++ show (s1e,s2e)

-- redundant because eq already includes this but just for excercise
sunif s1 s2 = do { subset s1 s2; subset s2 s1 }



subsets :: [a] -> [[a]]
subsets []  = [[]]
subsets (x:xs) = subsets xs ++ map (x:) (subsets xs)

