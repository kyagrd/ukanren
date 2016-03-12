-- vim: ts=2: sw=2: expandtab: ai:
{-# LANGUAGE FlexibleInstances #-}
module MicroKanren where

import Control.Applicative
import Control.Monad
import Control.Monad.State.Strict hiding (State)

import Data.List (sort)
import Data.Maybe (fromMaybe)
import Data.IntMap (IntMap)
import qualified Data.IntMap as IM

data Var = Var { varid::VarId, attr::Attr } deriving (Show, Eq, Ord)

type VarId = Int
type Attr = String

type Atom = String
-- newtype Atom = Int Int deriving (Show, Eq, Ord)

data Term = V Var
          | A Atom
          | L [Term]
            deriving (Show,Eq,Ord)


usort xs = uniq $ sort xs

uniq [] = []
uniq [x] = [x]
uniq (x:y:xs) | x == y    = uniq (y:xs)
              | otherwise = x : uniq (y:xs)

type Subst = IntMap Term
type State = (VarId, Subst)

--  A monad that can generate, bind, and look-up variables.
class Monad m => VarGen m where
    newVar :: Attr -> m Var
    assign :: VarId -> Term -> m ()
    deref :: VarId -> m (Maybe Term)

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
    newVar a = state (\(v,s) -> (Var v a, (v+1, s)))
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


-- expands variables at the top level until no change
expand :: Term -> K Term
expand t@(V v) = do t' <- fromMaybe t <$> deref (varid v)
                    if t' == t then return t else expand t'
expand t = return t

-- expands variables inside L and S
expand' :: Term -> K Term
expand' t@(V _) = do t' <- expand t
                     if t==t' then return t' else expand' t'
expand' t@(A _) = return t
expand' (L ts) = L <$> mapM expand' ts

fv_ (V x) = [x]
fv_ (A _) = []
fv_ (L ts) = concatMap fv_ ts

fv t = usort $ fv_ t

copy_term t t' = do
  te <- expand' t
  s <- sequence [(,) <$> pure v <*> newVar a | v@(Var _ a) <- fv te]
  t' `eq` subsvar s te
  te' <- expand' te
  return [p | p@(_,v) <- s, v `elem` fv te'] -- exclude irrelevant subs
  where
  subsvar s (V n) = V $ fromMaybe n (lookup n s)
  subsvar s t@(A _) = t
  subsvar s (L ts) = L $ map (subsvar s) ts


eq = eq_ (const True)

eq_ :: (Attr -> Bool) -> Term -> Term -> Goal
eq_ pa t1 t2 = join $ e <$> expand t1 <*> expand t2
  where
  e (V x) (V y) | x == y = ok
  e (V x) t | pa(attr x) = assign (varid x) t
  e t (V x) | pa(attr x) = assign (varid x) t
  e (A x) (A y) | (x == y) = ok
  e (L xs) (L ys) | length xs == length ys = zipWithM_ eq xs ys
  e _ _ = mzero

  -- hard-wired implemention of memb inside Kanren unification
  in_ t (z:zs) = e t z <|> do{ t/==z; in_ t zs } 
  in_ t [] = mzero


-- implemetation of Prolog's (/==)
(/==) :: Term -> Term -> Goal
a /== b = guard =<< (/=) <$> (expand a) <*> (expand b)

-- implemetation of Prolog's (==)
(===) :: Term -> Term -> Goal
a === b = guard =<< (==) <$> (expand a) <*> (expand b)



disj, conj :: Goal -> Goal -> Goal
disj = (<|>)
conj = (>>)

-- equivalent of disj+, conj+
disjs, conjs :: [Goal] -> Goal
disjs = msum
conjs = sequence_


-- Convenience function: fresh
class Fresh a where fresh :: Attr -> (a -> K b) -> K b
instance Fresh Var where fresh att f = newVar att >>= f
instance Fresh Term where fresh att f = fresh att (f . V)
instance (Fresh a, Fresh b) => Fresh (a,b) where
    fresh att f = fresh att (\a -> fresh att (\b -> f (a,b)))
instance (Fresh a, Fresh b, Fresh c) => Fresh (a,b,c) where
    fresh att f = fresh att (\a -> fresh att (\(b,c) -> f (a,b,c)))
instance (Fresh a, Fresh b, Fresh c, Fresh d) => Fresh (a,b,c,d) where
    fresh att f = fresh att (\(a,b) -> fresh att (\(c,d) -> f (a,b,c,d)))
instance (Fresh a, Fresh b, Fresh c, Fresh d, Fresh e) => Fresh (a,b,c,d,e) where
    fresh att f = fresh att (\(a,b,c) -> fresh att (\(d,e) -> f (a,b,c,d,e)))


fresh_ f = fresh "" f
-- Test cases
five :: Goal
five = fresh_ $ \x -> eq x (A "5")

fives :: Goal
fives = fresh_ fives_
-- where
fives_ x = eq x (A "5") <|> fives_ x

fivesR :: Goal
fivesR = fresh_ fivesR_
-- where
fivesR_ x = fivesR_ x <|> eq x (A "5")

aAndB :: Goal
aAndB = do fresh_ $ \a -> eq a (A "7")
           fresh_ $ \b -> eq b (A "5") <|> eq b (A "6")



test t = take 10 $ runK t start

tst t = mapM_ print $ test t


