-- vim: ts=2: sw=2: expandtab: ai:

import MicroKanren
import ExampleMember

import Control.Applicative
import Control.Monad

a_var = A "var"
a_app = A "app"
a_lam = A "lam"
a_let = A "let"
a_arr = A "arr"

a_mono = A "mono"
a_poly = A "poly"

mono t = L [a_mono, t]
poly c t = L [a_poly, c, t]

var x = L [a_var, x]
app t1 t2 = L [a_app, t1, t2]
lam x t = L [a_lam, x, t]
let_ x t0 t = L [a_let, x, t0, t]
arr a b = L [a_arr, a, b]

inst tsch t =
  do { tsch `eq` mono t }
  <|>
  ( fresh_ $ \(c,t1) -> do { tsch `eq` poly c t1
                          ; copy_term (poly c t1) (poly c t)
                          ; return () }
  )

type_ ctx tm ty =
  -- type(C, var(X), Ty) :- first(X:T, C), inst(T,Ty).
  ( fresh_ $ \(x,tsch) -> do{ tm `eq` var x
                           ; first x tsch ctx
                           ; inst tsch ty } )
  <|>
  -- type(C, app(F,E), Ty) :- type(C, F, arr(Te,Ty)), type(C,E,Te).
  ( fresh_ $ \(f, e, te) -> do{ tm `eq` app f e;
                             ; type_ ctx f (arr te ty) 
                             ; type_ ctx e te
                             } )
  <|>
  -- type(C, lam(X,E), arr(Tx,Ty)) :- type([mono(X):Tx)|C], E, Te).
  ( fresh_ $ \(x,tx,e,te) -> do{ tm `eq` lam x e
                              ; ty `eq` arr tx te
                              ; type_ (cons (pair x (mono tx)) ctx) e te
                              } )
  <|>
  -- type(C, let(X,E0,E), Ty) :- type(C,E0,Tx), type([poly(X:Tx)|C], E, Ty).
  ( fresh_ $ \(x,tm0,tx,e) -> do{ tm `eq` let_ x tm0 e
                               ; type_ ctx tm0 tx
                               ; type_ (cons (pair x (poly ctx tx)) ctx) e ty
                               } )


ex1 = tst $ fresh_ $ \ty -> do{ type_ nil (lam x $ var x) ty; expand' ty } where x = A"x"

ex2 = tst $ fresh_ $ \ty -> do{ type_ nil (lam x $ lam y $ var x) ty; expand' ty } where (x,y) = (A"x",A"y")

ex3 = tst $ fresh_ $ \ty -> do{ type_ nil (lam x $ lam y $ var y) ty; expand' ty } where (x,y) = (A"x",A"y")

tm_id = lam x (var x) where x = A "x"

ex9 = tst $ fresh_ $ \ty -> do{ type_ nil tm_id ty; expand' ty }

ex10 = tst $ fresh_ $ \ty -> do{ type_ nil (let_ f tm_id $ var f `app` var f) ty; expand' ty } where f = A"f"


