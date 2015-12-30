-- vim: ts=2: sw=2: expandtab: ai:

import MicroKanren
import ExampleMember

import Control.Applicative
import Control.Monad

a_var = A "var"
a_app = A "app"
a_lam = A "lam"
a_arr = A "arr"

var x = L [a_var, x]
app t1 t2 = L [a_app, t1, t2]
lam x t = L [a_lam, x, t]
arr a b = L [a_arr, a, b]

type_ ctx tm ty =
  -- type(C, var(X), Ty) :- first(X:Ty, C).
  ( fresh $ \x -> do{ tm `eq` var x; first x ty ctx } )
  <|>
  -- type(C, app(F,E), Ty) :- type(C, F, arr(Te,Ty)), type(C,E,Te).
  ( fresh $ \(f, e, te) -> do{ tm `eq` app f e;
                             ; type_ ctx f (arr te ty) 
                             ; type_ ctx e te
                             } )
  <|>
  -- type(C, lam(X,E), arr(Tx,Ty)) :- type([(X:Tx)|C], E, Te).
  ( fresh $ \(x,tx,e,te) -> do{ tm `eq` lam x e
                              ; ty `eq` arr tx te
                              ; type_ (cons (pair x tx) ctx) e te
                              } )


ex1 = tst $ fresh $ \ty -> do{ type_ nil (lam x $ var x) ty; expand' ty } where x = A"x"

ex2 = tst $ fresh $ \ty -> do{ type_ nil (lam x $ lam y $ var x) ty; expand' ty } where (x,y) = (A"x",A"y")

ex3 = tst $ fresh $ \ty -> do{ type_ nil (lam x $ lam y $ var y) ty; expand' ty } where (x,y) = (A"x",A"y")

