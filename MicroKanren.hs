-- vim: ts=2: sw=2: expandtab: ai:
{-# LANGUAGE FlexibleInstances #-}
module MicroKanren where

import Control.Applicative
import Control.Monad
import Control.Monad.State.Strict hiding (State)

import Data.Maybe (fromMaybe)
import Data.IntMap (IntMap)
import qualified Data.IntMap as IM

type Var = Int

type Atom = String
-- data Atom = Int Int
--        deriving (Show, Eq, Ord)

data Term = V Var
          | A Atom
          | L [Term]
            deriving (Show, Eq, Ord)

type Subst = IntMap Term
type State = (Var, Subst)

--  A monad that can generate, bind, and look-up variables.
class Monad m => VarGen m where
    newVar :: m Var
    assign :: Var -> Term -> m ()
    deref :: Var -> m (Maybe Term)

-- Fair interleaving of finitely many lists.
interleaves :: [[a]] -> [a]
interleaves [] = []
interleaves l = [x | x:_ <- l] ++ interleaves [xs | _:xs <- l]

interleave :: [a] -> [a] -> [a]
interleave a b = interleaves [a,b]


-- Search trees, so we can define the search algorithm separately.
data Tree a = Empty | Single a | Node (Tree a) (Tree a) deriving Show

instance Functor Tree where fmap = liftM
instance Applicative Tree where pure = return; (<*>) = ap
instance Monad Tree where
    return = Single
    Empty >>= _ = Empty
    Single x >>= f = f x
    Node l r >>= f = Node (l >>= f) (r >>= f)

-- NB. not a law-abiding Alternative/MonadPlus instance: not associative.
instance MonadPlus Tree where mzero = empty; mplus = (<|>)
instance Alternative Tree where empty = Empty; (<|>) = Node


-- Search strategies over Trees.
listify :: ([a] -> [a] -> [a]) -> Tree a -> [a]
listify _ Empty = []
listify _ (Single a) = [a]
listify f (Node l r) = f (listify f l) (listify f r)

dfs, ifs, bfs :: Tree a -> [a]

dfs = listify (++)

-- Not sure if there's a standard name for this search strategy.
ifs = listify interleave

-- Unfortunately we can't write iterated deepening as a function on Trees,
-- because of Haskell's memoizing call-by-need evaluation. So we'll just do a
-- plain old memory-hogging BFS.
bfs t = search [] [t]
    -- we use the usual trick of encoding a queue as two stacks.
    where search [] [] = []
          search a [] = search [] (reverse a)
          search a (Empty : b) = search a b
          search a (Single x : b) = x : search a b
          search a (Node l r : b) = search (r:l:a) b


-- Implementation of the Kanren interface
type K = StateT State Tree
type Goal = K ()

instance Monad m => VarGen (StateT State m) where
    newVar = state (\(v,s) -> (v, (v+1, s)))
    assign v t = modify (fmap (IM.insert v t))
    deref v = gets (\(_,sub) -> IM.lookup v sub)

start :: State
start = (0, IM.empty)

runK :: K a -> State -> [(a, State)]
runK k st = bfs $ runStateT k st
-- NB. if we change bfs to ifs, then fivesR fails!
-- with dfs you get prolog-like behavior, and even more things fail.

evalK :: K a -> State -> [a]
evalK k st = map fst (runK k st)

execK :: K a -> State -> [State]
execK k st = map snd (runK k st)


-- Basic operators.
ok :: Goal
ok = pure ()

expand :: Term -> K Term
expand t@(V v) = fromMaybe t <$> deref v
expand t = return t

eq :: Term -> Term -> Goal
eq t1 t2 = join $ e <$> expand t1 <*> expand t2
    where
      e (V x) (V y) | x == y = ok
      e (V x) t = assign x t
      e t (V x) = assign x t
      e (A x) (A y) | (x == y) = ok
      e (L xs) (L ys) | length xs == length ys = zipWithM_ eq xs ys
      e _ _ = mzero

disj, conj :: Goal -> Goal -> Goal
disj = (<|>)
conj = (>>)

-- equivalent of disj+, conj+
disjs, conjs :: [Goal] -> Goal
disjs = msum
conjs = sequence_


-- Convenience function: fresh
class Fresh a where fresh :: (a -> K b) -> K b
instance Fresh Var where fresh f = newVar >>= f
instance Fresh Term where fresh f = fresh (f . V)
instance (Fresh a, Fresh b) => Fresh (a,b) where
    fresh f = fresh (\a -> fresh (\b -> f (a,b)))
instance (Fresh a, Fresh b, Fresh c) => Fresh (a,b,c) where
    fresh f = fresh (\a -> fresh (\(b,c) -> f (a,b,c)))
instance (Fresh a, Fresh b, Fresh c, Fresh d) => Fresh (a,b,c,d) where
    fresh f = fresh (\(a,b) -> fresh (\(c,d) -> f (a,b,c,d)))
instance (Fresh a, Fresh b, Fresh c, Fresh d, Fresh e) => Fresh (a,b,c,d,e)where
    fresh f = fresh (\(a,b,c) -> fresh (\(d,e) -> f (a,b,c,d,e)))


-- Test cases
five :: Goal
five = fresh $ \x -> eq x (A "5")

fives :: Goal
fives = fresh fives_
-- where
fives_ x = eq x (A "5") <|> fives_ x

fivesR :: Goal
fivesR = fresh fivesR_
-- where
fivesR_ x = fivesR_ x <|> eq x (A "5")

aAndB :: Goal
aAndB = do fresh $ \a -> eq a (A "7")
           fresh $ \b -> eq b (A "5") <|> eq b (A "6")


-- for building list terms
nil :: Term
nil = A "nil"
cons :: Term -> Term -> Term
cons x xs = L [A "cons", x, xs]



-- Prolog's usual list membership
--
-- member(A,[A|_ ]).
-- member(A,[X|Xs]) :- member(X,Xs).
--
member :: Term -> Term -> Goal
member a s = fresh $ \(x,xs) -> eq s (cons a xs) <|>
                            do{ eq s (cons x xs); member a xs }
{-
*MicroKanren> tst (A"a" `member` cons (A"a") nil)
((),(2,fromList [(1,A "nil")]))

*MicroKanren> tst (fresh $ \xs -> A"a" `member` cons (A"a") xs)
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

*MicroKanren> tst (fresh $ \(x,xs) -> A"a" `member` cons x xs)
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

-- list membrership with, an alternative implentation
membr :: Term -> Term -> Goal
membr a s = fresh $ \(x,xs) -> eq s (cons x xs) >> (eq a x <|> membr a xs)

{-
*MicroKanren> tst (A"a" `membr` cons (A"a") nil)
((),(2,fromList [(0,A "a"),(1,A "nil")]))

*MicroKanren> tst (fresh $ \xs -> A"a" `membr` cons (A"a") xs)
((),(3,fromList [(0,V 2),(1,A "a")]))
((),(5,fromList [(0,V 2),(1,A "a"),(2,L [A "cons",V 3,V 4]),(3,A "a")]))
((),(7,fromList [(0,V 2),(1,A "a"),(2,L [A "cons",V 3,V 4]),(4,L [A "cons",V 5,V 6]),(5,A "a")]))
((),(9,fromList [(0,V 2),(1,A "a"),(2,L [A "cons",V 3,V 4]),(4,L [A "cons",V 5,V 6]),(6,L [A "cons",V 7,V 8]),(7,A "a")]))
((),(11,fromList [(0,V 2),(1,A "a"),(2,L [A "cons",V 3,V 4]),(4,L [A "cons",V 5,V 6]),(6,L [A "cons",V 7,V 8]),(8,L [A "cons",V 9,V 10]),(9,A "a")]))
((),(13,fromList [(0,V 2),(1,A "a"),(2,L [A "cons",V 3,V 4]),(4,L [A "cons",V 5,V 6]),(6,L [A "cons",V 7,V 8]),(8,L [A "cons",V 9,V 10]),(10,L [A "cons",V 11,V 12]),(11,A "a")]))
((),(15,fromList [(0,V 2),(1,A "a"),(2,L [A "cons",V 3,V 4]),(4,L [A "cons",V 5,V 6]),(6,L [A "cons",V 7,V 8]),(8,L [A "cons",V 9,V 10]),(10,L [A "cons",V 11,V 12]),(12,L [A "cons",V 13,V 14]),(13,A "a")]))
((),(17,fromList [(0,V 2),(1,A "a"),(2,L [A "cons",V 3,V 4]),(4,L [A "cons",V 5,V 6]),(6,L [A "cons",V 7,V 8]),(8,L [A "cons",V 9,V 10]),(10,L [A "cons",V 11,V 12]),(12,L [A "cons",V 13,V 14]),(14,L [A "cons",V 15,V 16]),(15,A "a")]))
((),(19,fromList [(0,V 2),(1,A "a"),(2,L [A "cons",V 3,V 4]),(4,L [A "cons",V 5,V 6]),(6,L [A "cons",V 7,V 8]),(8,L [A "cons",V 9,V 10]),(10,L [A "cons",V 11,V 12]),(12,L [A "cons",V 13,V 14]),(14,L [A "cons",V 15,V 16]),(16,L [A "cons",V 17,V 18]),(17,A "a")]))
((),(21,fromList [(0,V 2),(1,A "a"),(2,L [A "cons",V 3,V 4]),(4,L [A "cons",V 5,V 6]),(6,L [A "cons",V 7,V 8]),(8,L [A "cons",V 9,V 10]),(10,L [A "cons",V 11,V 12]),(12,L [A "cons",V 13,V 14]),(14,L [A "cons",V 15,V 16]),(16,L [A "cons",V 17,V 18]),(18,L [A "cons",V 19,V 20]),(19,A "a")]))

*MicroKanren> tst (fresh $ \(x,xs) -> A"a" `membr` cons x xs)
((),(4,fromList [(0,V 2),(1,V 3),(2,A "a")]))
((),(6,fromList [(0,V 2),(1,V 3),(3,L [A "cons",V 4,V 5]),(4,A "a")]))
((),(8,fromList [(0,V 2),(1,V 3),(3,L [A "cons",V 4,V 5]),(5,L [A "cons",V 6,V 7]),(6,A "a")]))
((),(10,fromList [(0,V 2),(1,V 3),(3,L [A "cons",V 4,V 5]),(5,L [A "cons",V 6,V 7]),(7,L [A "cons",V 8,V 9]),(8,A "a")]))
((),(12,fromList [(0,V 2),(1,V 3),(3,L [A "cons",V 4,V 5]),(5,L [A "cons",V 6,V 7]),(7,L [A "cons",V 8,V 9]),(9,L [A "cons",V 10,V 11]),(10,A "a")]))
((),(14,fromList [(0,V 2),(1,V 3),(3,L [A "cons",V 4,V 5]),(5,L [A "cons",V 6,V 7]),(7,L [A "cons",V 8,V 9]),(9,L [A "cons",V 10,V 11]),(11,L [A "cons",V 12,V 13]),(12,A "a")]))
((),(16,fromList [(0,V 2),(1,V 3),(3,L [A "cons",V 4,V 5]),(5,L [A "cons",V 6,V 7]),(7,L [A "cons",V 8,V 9]),(9,L [A "cons",V 10,V 11]),(11,L [A "cons",V 12,V 13]),(13,L [A "cons",V 14,V 15]),(14,A "a")]))
((),(18,fromList [(0,V 2),(1,V 3),(3,L [A "cons",V 4,V 5]),(5,L [A "cons",V 6,V 7]),(7,L [A "cons",V 8,V 9]),(9,L [A "cons",V 10,V 11]),(11,L [A "cons",V 12,V 13]),(13,L [A "cons",V 14,V 15]),(15,L [A "cons",V 16,V 17]),(16,A "a")]))
((),(20,fromList [(0,V 2),(1,V 3),(3,L [A "cons",V 4,V 5]),(5,L [A "cons",V 6,V 7]),(7,L [A "cons",V 8,V 9]),(9,L [A "cons",V 10,V 11]),(11,L [A "cons",V 12,V 13]),(13,L [A "cons",V 14,V 15]),(15,L [A "cons",V 16,V 17]),(17,L [A "cons",V 18,V 19]),(18,A "a")]))
((),(22,fromList [(0,V 2),(1,V 3),(3,L [A "cons",V 4,V 5]),(5,L [A "cons",V 6,V 7]),(7,L [A "cons",V 8,V 9]),(9,L [A "cons",V 10,V 11]),(11,L [A "cons",V 12,V 13]),(13,L [A "cons",V 14,V 15]),(15,L [A "cons",V 16,V 17]),(17,L [A "cons",V 18,V 19]),(19,L [A "cons",V 20,V 21]),(20,A "a")]))
-}

test t = take 10 $ runK t start

tst t = mapM_ print $ test t

