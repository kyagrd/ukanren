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
  -- type(Ctx, var(X), Ty) :- first (X:Ty) Ctx.
  ( fresh $ \x -> do{ tm `eq` var x; first x ty ctx } )
  <|>
  -- type(Ctx, app(F,E), Ty) :- type(Ctx, F, arr(Te,Ty)), type(Ctx,E,Te).
  ( fresh $ \(f, e, te) -> do{ tm `eq` app f e;
                             ; type_ ctx f (arr te ty) 
                             ; type_ ctx e te
                             } )
  <|>
  -- type(Ctx, lam(X,E), arr(Tx,Ty)) :- type([(X:Tx)|Ctx], E, Te).
  ( fresh $ \(x,tx,e,te) -> do{ tm `eq` lam x e
                              ; ty `eq` arr tx te
                              ; type_ (cons (pair x tx) ctx) e te
                              } )
