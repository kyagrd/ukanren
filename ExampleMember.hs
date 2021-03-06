-- vim: ts=2: sw=2: expandtab: ai:
module ExampleMember where

import MicroKanren

import Control.Applicative
import Control.Monad

-- for building list terms
nil :: Term
nil = a_nil
cons :: Term -> Term -> Term
cons x xs = L [a_cons, x, xs]

a_nil = A "nil"
a_cons = A "cons"

-- Prolog's usual list membership
--
-- member(A,[A|_ ]).
-- member(A,[X|Xs]) :- member(A,Xs).
--
member :: Term -> Term -> Goal
member a s = fresh_ $ \(x,xs) -> eq s (cons a xs) <|>
                             do{ eq s (cons x xs); member a xs }
{-
*ExampleMember> :m + MicroKanren

*ExampleMember MicroKanren> tst (A"a" `member` cons (A"a") nil)
((),(2,fromList [(1,A "nil")]))

*ExampleMember MicroKanren> tst (fresh_ $ \xs -> A"a" `member` cons (A"a") xs)
((),(3,fromList [(0,V 2)]))
((),(5,fromList [(0,V 2),(1,A "a"),(2,L [A "cons",A "a",V 4])]))
((),(7,fromList [(0,V 2),(1,A "a"),(2,L [A "cons",V 3,V 4]),(4,L [A "cons",A "a",V 6])]))
((),(9,fromList [(0,V 2),(1,A "a"),(2,L [A "cons",V 3,V 4]),(4,L [A "cons",V 5,V 6]),(6,L [A "cons",A "a",V 8])]))
((),(11,fromList [(0,V 2),(1,A "a"),(2,L [A "cons",V 3,V 4]),(4,L [A "cons",V 5,V 6]),(6,L [A "cons",V 7,V 8]),(8,L [A "cons",A "a",V 10])]))
((),(13,fromList [(0,V 2),(1,A "a"),(2,L [A "cons",V 3,V 4]),(4,L [A "cons",V 5,V 6]),(6,L [A "cons",V 7,V 8]),(8,L [A "cons",V 9,V 10]),(10,L [A "cons",A "a",V 12])]))
((),(15,fromList [(0,V 2),(1,A "a"),(2,L [A "cons",V 3,V 4]),(4,L [A "cons",V 5,V 6]),(6,L [A "cons",V 7,V 8]),(8,L [A "cons",V 9,V 10]),(10,L [A "cons",V 11,V 12]),(12,L [A "cons",A "a",V 14])]))
((),(17,fromList [(0,V 2),(1,A "a"),(2,L [A "cons",V 3,V 4]),(4,L [A "cons",V 5,V 6]),(6,L [A "cons",V 7,V 8]),(8,L [A "cons",V 9,V 10]),(10,L [A "cons",V 11,V 12]),(12,L [A "cons",V 13,V 14]),(14,L [A "cons",A "a",V 16])]))
((),(19,fromList [(0,V 2),(1,A "a"),(2,L [A "cons",V 3,V 4]),(4,L [A "cons",V 5,V 6]),(6,L [A "cons",V 7,V 8]),(8,L [A "cons",V 9,V 10]),(10,L [A "cons",V 11,V 12]),(12,L [A "cons",V 13,V 14]),(14,L [A "cons",V 15,V 16]),(16,L [A "cons",A "a",V 18])]))
((),(21,fromList [(0,V 2),(1,A "a"),(2,L [A "cons",V 3,V 4]),(4,L [A "cons",V 5,V 6]),(6,L [A "cons",V 7,V 8]),(8,L [A "cons",V 9,V 10]),(10,L [A "cons",V 11,V 12]),(12,L [A "cons",V 13,V 14]),(14,L [A "cons",V 15,V 16]),(16,L [A "cons",V 17,V 18]),(18,L [A "cons",A "a",V 20])]))

*ExampleMember MicroKanren> tst (fresh_ $ \(x,xs) -> A"a" `member` cons x xs)
((),(4,fromList [(0,A "a"),(1,V 3)]))
((),(6,fromList [(0,V 2),(1,V 3),(3,L [A "cons",A "a",V 5])]))
((),(8,fromList [(0,V 2),(1,V 3),(3,L [A "cons",V 4,V 5]),(5,L [A "cons",A "a",V 7])]))
((),(10,fromList [(0,V 2),(1,V 3),(3,L [A "cons",V 4,V 5]),(5,L [A "cons",V 6,V 7]),(7,L [A "cons",A "a",V 9])]))
((),(12,fromList [(0,V 2),(1,V 3),(3,L [A "cons",V 4,V 5]),(5,L [A "cons",V 6,V 7]),(7,L [A "cons",V 8,V 9]),(9,L [A "cons",A "a",V 11])]))
((),(14,fromList [(0,V 2),(1,V 3),(3,L [A "cons",V 4,V 5]),(5,L [A "cons",V 6,V 7]),(7,L [A "cons",V 8,V 9]),(9,L [A "cons",V 10,V 11]),(11,L [A "cons",A "a",V 13])]))
((),(16,fromList [(0,V 2),(1,V 3),(3,L [A "cons",V 4,V 5]),(5,L [A "cons",V 6,V 7]),(7,L [A "cons",V 8,V 9]),(9,L [A "cons",V 10,V 11]),(11,L [A "cons",V 12,V 13]),(13,L [A "cons",A "a",V 15])]))
((),(18,fromList [(0,V 2),(1,V 3),(3,L [A "cons",V 4,V 5]),(5,L [A "cons",V 6,V 7]),(7,L [A "cons",V 8,V 9]),(9,L [A "cons",V 10,V 11]),(11,L [A "cons",V 12,V 13]),(13,L [A "cons",V 14,V 15]),(15,L [A "cons",A "a",V 17])]))
((),(20,fromList [(0,V 2),(1,V 3),(3,L [A "cons",V 4,V 5]),(5,L [A "cons",V 6,V 7]),(7,L [A "cons",V 8,V 9]),(9,L [A "cons",V 10,V 11]),(11,L [A "cons",V 12,V 13]),(13,L [A "cons",V 14,V 15]),(15,L [A "cons",V 16,V 17]),(17,L [A "cons",A "a",V 19])]))
((),(22,fromList [(0,V 2),(1,V 3),(3,L [A "cons",V 4,V 5]),(5,L [A "cons",V 6,V 7]),(7,L [A "cons",V 8,V 9]),(9,L [A "cons",V 10,V 11]),(11,L [A "cons",V 12,V 13]),(13,L [A "cons",V 14,V 15]),(15,L [A "cons",V 16,V 17]),(17,L [A "cons",V 18,V 19]),(19,L [A "cons",A "a",V 21])]))
-}

-- list membrership with, an alternative implentation.
-- Result is similar to above member but a bit different
-- in order/number of nfresh variable generation. Cannot prove it
-- but I think membr and member are eqivalent modulo fresh variables.
membr :: Term -> Term -> Goal
membr a s = fresh_ $ \(x,xs) -> eq s (cons x xs) >> (eq a x <|> membr a xs)


-- list membrership with guarded by (/==) in Prolog.
-- Reduces search space in case of quering an uninstantiated variable
-- and the list happens to contain that same variable.
-- 
-- memb(A,[A|_ ]).
-- memb(A,[X|Xs]) :- A /== X, memb(A,Xs).
--
memb :: Term -> Term -> Goal
memb a s = fresh_ $ \(x,xs) -> eq s (cons a xs) <|>
                          do{ eq s (cons x xs); a /== x; memb a xs }
{-
*ExampleMember MicroKanren> tst (fresh_ $ \(x,xs) -> x `memb` cons x xs)
((),(4,fromList [(1,V 3)]))
 -}

a_pair = A "pair"
pair x y = L [a_pair, x, y] 

first :: Term -> Term -> Term -> Goal
first k v ctx = fresh_ $ \(k1,v1,ps) ->
  do { ctx `eq` cons (pair k1 v1) ps
     ; do { k `eq` k1; v `eq` v1 } <|>
       do { k /== k1; first k v ps }
     }




-----------------------------------------------------------

-- for building list terms
snil :: Term
snil = a_snil
scons :: Term -> Term -> Term
scons x xs = L [a_scons, x, xs]

a_snil = A "{}"
a_scons = A "{|}"

smemb :: Term -> Term -> Goal
smemb a s = fresh_ $ \(x,xs) -> eq s (scons a xs) <|>
                           do{ eq s (scons x xs); a /== x; smemb a xs }


-- finite subset
subset_of :: Term -> Term -> Goal
subset_of s1 s2 = fresh_ $ \(x,xs) ->
  eq s1 snil <|> do { s1 `eq` scons x xs; smemb x s2; subset_of xs s2 }

-- finite set unificaiton
sunify :: Term -> Term -> Goal
sunify s1 s2 = do { subset_of s1 s2; subset_of s2 s1 }

-- appending sets as lists
sapp :: Term -> Term -> Term -> Goal
sapp xs ys zs =
  do { xs `eq` snil; ys `eq` zs }
  <|>
  ( fresh_ $ \(x,ts,us) ->
      do { xs `eq` scons x ts; zs `eq` scons x us; sapp ts ys us } )


-- naive implementation
osunify :: Term -> Term -> Goal
osunify s1 s2 = do
  s1e <- expand' s1
  s2e <- expand' s2
  case (s1e,s2e) of
    (V _, _) -> s1e `eq` s2e
    (_, V _) -> s1e `eq` s2e
    _ -> fresh_ $ \(xs,t1,ys,t2) ->
      do { split_heads s1e (xs,t1)
         ; split_heads s2e (ys,t2)
         ; osu (xs,t1) (ys,t2)
         }

split_heads s (xs,t) = -- we know that s is not variable
  do { s `eq` snil; xs `eq` snil; t `eq` snil }
  <|>
  ( fresh_ $ \(y,ys) ->
      do { s `eq` scons y ys
         ; ys_ <- expand ys
         ; case ys_ of
             V _ -> do { xs `eq` scons y snil; t `eq` ys }
             _   -> fresh_ $ \hs ->
                    do { xs `eq` scons y hs; split_heads ys (hs,t) }
         } )

osu (xs,t1) (ys,t2) = do
  t1e <- expand' t1
  t2e <- expand' t2
  if t1e==snil && t2e==snil then sunify xs ys
  else if t1e==snil then do { subset_of ys xs; t2 `eq` xs }
  else if t2e==snil then do { subset_of xs ys; t1 `eq` ys }
  else fresh_ $ \(zs,t) -> do { sapp xs ys zs; sapp zs t t1; sapp zs t t2 }

