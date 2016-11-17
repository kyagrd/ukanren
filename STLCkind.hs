-- vim: ts=2: sw=2: expandtab: ai:
{-# LANGUAGE FlexibleInstances #-}

import MicroKanren hiding (fresh, fresh_)
import qualified MicroKanren (fresh_)
import ExampleMember

import Control.Applicative
import Control.Monad

fresh f = MicroKanren.fresh_ f

a_var = A "var"
a_app = A "app"
a_lam = A "lam"
a_arr = A "arr"
a_o = A "o"

var x = L [a_var, x]
app t1 t2 = L [a_app, t1, t2]
lam x t = L [a_lam, x, t]
arr a b = L [a_arr, a, b]

star = L [a_o]


kind_ kc t k =
  -- kind(KC, var(X), K) :- first (X:K) KC.
  ( fresh $ \x -> do{ t `eq` var x; first x k kc } )
  <|>
  -- kind(KC, app(F,A), K) :- kind(KC, F, arr(Ka,K)), kind(KC,A,Ka).
  ( fresh $ \(f, a, ka) -> do{ t `eq` app f a;
                             ; kind_ kc f (arr ka k) 
                             ; kind_ kc a ka
                             } )
  <|>
  -- kind(KC, arr(A,B), o) :- kind(KC, A, star), kind(KC,B,star).
  ( fresh $ \(a, b) -> do{ t `eq` arr a b
                         ; k `eq` star
                         ; kind_ kc a star
                         ; kind_ kc b star
                         } )



type_ kc ctx tm ty =
  -- type(KC, C, var(X), Ty) :- first(X:Ty, C).
  ( fresh $ \x -> do{ tm `eq` var x; first x ty ctx; return [] } )
  <|>
  -- type(KC, C, app(F,E), Ty) :- type(C, F, arr(Te,Ty)), type(C,E,Te).
  ( fresh $ \(f, e, te) -> do{ tm `eq` app f e;
                             ; gs1 <- type_ kc ctx f (arr te ty)
                             ; gs2 <- type_ kc ctx e te
                             ; return $ gs1++gs2
                             } )
  <|>
  -- type(KC, C, lam(X,E), arr(Tx,Te)) :- type(KC, [(X:Tx)|C], E, Te),
  --                                      kind(KC, arr(Tx,Te), o).
  ( fresh $ \(x,tx,e,te) -> do{ tm `eq` lam x e
                              ; ty `eq` arr tx te
                              ; gs <- type_ kc (cons (pair x tx) ctx) e te
                              ; return (L[A"kind",kc,arr tx te,star] : gs)
                              } )

ex1 = tst $ fresh $ \(kc,ty) ->
  do gs <- type_ kc nil (lam x $ var x) ty
     ty_ <- expand' ty
     conjs [V x `eq` var(A $ "_"++show x) | x <- fv ty_] -- concretize vars
     conjs [kind_ kctx t k | L[A"kind",kctx,t,k] <- gs] -- run delayed goal
     (,) <$> expand' ty <*> expand' kc
  where x = A "x"

ex2 = tst $ fresh $ \(kc,ty) ->
  do gs <- type_ kc nil (lam x $ lam y $ var x) ty;
     ty_ <- expand' ty
     conjs [V x `eq` var(A $ "_"++show x) | x <- fv ty_] -- concretize vars
     conjs [kind_ kctx t k | L[A"kind",kctx,t,k] <- gs] -- run delayed goal
     (,) <$> expand' ty <*> expand' kc
  where (x,y) = (A"x",A"y")


ex3 = tst $ fresh $ \(kc,ty) ->
  do gs <- type_ kc nil (lam x $ lam y $ var y) ty;
     ty_ <- expand' ty
     conjs [V x `eq` var(A $ "_"++show x) | x <- fv ty_] -- concretize vars
     conjs [kind_ kctx t k | L[A"kind",kctx,t,k] <- gs] -- run delayed goal
     (,) <$> expand' ty <*> expand' kc
  where (x,y) = (A"x",A"y")



ex10 = let (a,b) = (V(Var (-1) ""),V(Var (-2) "")) in tst $ fresh $ \kc -> do{ kind_ kc (arr a b) star; kc' <- expand' kc; a' <- expand' a; b' <- expand' b; return (a',b',kc') }
