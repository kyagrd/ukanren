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

type Var = Int

type Atom = String
-- data Atom = Int Int
--        deriving (Show, Eq, Ord)

data Term = V Var
          | A Atom
          | L [Term]
          | S [Term]
            deriving (Show)


-- there may be a generic programming solution to these Eq and Ord instances

instance Eq Term where
  V x  == V y  = x==y
  A a  == A b  = a==b
  L ts == L us = and $ zipWith (==) ts us
  S ts == S us = usort ts == usort us
  _    == _    = False

instance Ord Term where
   V x  <= V y  = x <= y
   V _  <= _    = True
   A _  <= V _  = False
   A a  <= A b  = a <= b
   A _  <= _    = True
   L _  <= V _  = False
   L _  <= A _  = False
   L ts <= L us = ts <= us
   L _  <= _    = True
   S ts <= S us = usort ts <= usort us
   S _  <= _    = False

   V x  < V y  = x < y
   V _  < _    = True
   A a  < A b  = a < b
   A _  < _    = True
   L _  < V _  = False
   L _  < A _  = False
   L ts < L us = ts < us
   L _  < _    = True
   S ts < S us = usort ts < usort us
   S _  < _    = False


usort xs = uniq $ sort xs

uniq [] = []
uniq [x] = [x]
uniq (x:y:xs) | x == y    = uniq (y:xs)
              | otherwise = x : uniq (y:xs)

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

-- expands variables at the top level until no change
expand :: Term -> K Term
expand t@(V v) = do t' <- fromMaybe t <$> deref v
                    if t' == t then return t else expand t'
expand t = return t

-- expands variables inside L and S
expand' :: Term -> K Term
expand' t@(V _) = do t' <- expand t
                     if t==t' then return t' else expand' t'
expand' t@(A _) = return t
expand' (L ts) = L <$> mapM expand' ts
expand' (S ts) = S <$> mapM expand' ts

fv_ (V x) = [x]
fv_ (A _) = []
fv_ (L ts) = concatMap fv_ ts
fv_ (S ts) = concatMap fv_ ts

fv t = usort $ fv_ t

copy_term t t' = do
  te <- expand' t
  s <- sequence [(,) <$> pure v <*> newVar | v <- fv te]
  t' `eq` subsvar s te
  te' <- expand' te
  return [p | p@(_,v) <- s, v `elem` fv te'] -- exclude irrelevant subs
  where
  subsvar s (V n) = V $ fromMaybe n (lookup n s)
  subsvar s t@(A _) = t
  subsvar s (L ts) = L $ map (subsvar s) ts
  subsvar s (S ts) = S $ map (subsvar s) ts

-- Finite set unification baked in but this way cannot do set union
-- set member, etc, in a logical way. Only unification ...
eq :: Term -> Term -> Goal
eq t1 t2 = join $ e <$> expand t1 <*> expand t2
    where
      e (V x) (V y) | x == y = ok
      e (V x) t = assign x t
      e t (V x) = assign x t
      e (A x) (A y) | (x == y) = ok
      e (L xs) (L ys) | length xs == length ys = zipWithM_ eq xs ys
      -- hack to make ex10 and ex10' stop looping instead of calling
      -- eq inside in_ function but is this really ok? Maybe having
      -- an occurs check by default might be the right way?
      e (S xs) (S ys) = do xs' <- usort <$> mapM expand xs
                           ys' <- usort <$> mapM expand ys
                           conjs $ interleave [x `in_` ys'|x<-xs']
                                              [y `in_` xs'|y<-ys']
      e _ _ = mzero
      -- hard-wired implemention of memb inside Kanren unification
      in_ t (z:zs) = e t z <|> do{ t/==z; in_ t zs } 
      in_ t [] = mzero
{-
      e (S xs) (S ys) = conjs $ interleave [x `in_` ys'|x<-xs']
                                           [y `in_` xs'|y<-ys']
                      where xs' = usort xs
                            ys' = usort ys
      e _ _ = mzero
-}

-- implemetation of Prolog's (/==) in microKanren
(/==) :: Term -> Term -> Goal
a /== b = guard =<< (/=) <$> (expand a) <*> (expand b)

-- implemetation of Prolog's (==) in microKanren
(===) :: Term -> Term -> Goal
a === b = guard =<< (==) <$> (expand a) <*> (expand b)

{-
          do a' <- expand a
             b' <- expand b
             guard (a' /= b')
-}  

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
instance (Fresh a, Fresh b, Fresh c, Fresh d, Fresh e) => Fresh (a,b,c,d,e) where
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



test t = take 10 $ runK t start

tst t = mapM_ print $ test t


---------------------------------------------------------------

{- finite set unification
*MicroKanren> tst (fresh $ \(x,y) -> do{S [y,x] `eq` S [x,y]})
((),(2,fromList [(1,V 0)]))
((),(2,fromList [(0,V 1)]))
((),(2,fromList []))
*MicroKanren> tst (fresh $ \(x,y) -> do{x `eq` A"a";S [y,x] `eq` S [x,y]})
((),(2,fromList [(0,A "a"),(1,A "a")]))
((),(2,fromList [(0,A "a"),(1,A "a")]))
((),(2,fromList [(0,A "a")]))
*MicroKanren> tst (fresh $ \(x,y) -> do{x `eq` A"a";S [y,x] `eq` S [x,y];y `eq` A"b"})
((),(2,fromList [(0,A "a"),(1,A "b")]))
-}

