-- vim: ts=2: sw=2: expandtab: ai:
module ExampleMember where

import MicroKanren

import Control.Applicative
import Control.Monad

-- for building list terms
nil :: Term
nil = A "nil"
cons :: Term -> Term -> Term
cons x xs = L [A "cons", x, xs]


-- Prolog's usual list membership
--
-- member(A,[A|_ ]).
-- member(A,[X|Xs]) :- member(A,Xs).
--
member :: Term -> Term -> Goal
member a s = fresh $ \(x,xs) -> eq s (cons a xs) <|>
                            do{ eq s (cons x xs); member a xs }
{-
*ExampleMember> :m + MicroKanren

*ExampleMember MicroKanren> tst (A"a" `member` cons (A"a") nil)
((),(2,fromList [(1,A "nil")]))

*ExampleMember MicroKanren> tst (fresh $ \xs -> A"a" `member` cons (A"a") xs)
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

*ExampleMember MicroKanren> tst (fresh $ \(x,xs) -> A"a" `member` cons x xs)
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
membr a s = fresh $ \(x,xs) -> eq s (cons x xs) >> (eq a x <|> membr a xs)


-- list membrership with guarded by (/==) in Prolog.
-- Reduces search space in case of quering an uninstantiated and the list
-- happens to contain that same variable.
-- 
-- memb(A,[A|_ ]).
-- memb(A,[X|Xs]) :- A /== X, memb(A,Xs).
--
memb :: Term -> Term -> Goal
memb a s = fresh $ \(x,xs) -> eq s (cons a xs) <|>
                          do{ eq s (cons x xs); a /== x; memb a xs }
{-
*ExampleMember MicroKanren> tst (fresh $ \(x,xs) -> x `memb` cons x xs)
((),(4,fromList [(1,V 3)]))
 -}

-- implemetation of Prolog's (/==) in microKanren
(/==) :: Term -> Term -> Goal
a /== b = do a_ <- expand a
             b_ <- expand b
             guard (a_ /= b_)

