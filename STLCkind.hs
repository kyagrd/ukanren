-- vim: ts=2: sw=2: expandtab: ai:

import MicroKanren
import ExampleMember

import Control.Applicative
import Control.Monad

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
                             ; type_ kc a ka
                             } )
  <|>
  -- kind(KC, arr(A,B), o) :- kind(KC, A, star), kind(KC,B,star).
  ( fresh $ \(a, b) -> do{ t `eq` arr a b
                         ; k `eq` star
                         ; kind_ kc a star
                         ; kind_ kc b star
                         } )



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

ex3 = tst $ fresh $ \(x,y,ty) -> do{ type_ nil (lam x $ lam y $ var y) ty; expand' ty }

ex10 = let (a,b) = (V(-1),V(-2)) in tst $ fresh $ \kc -> do { kind_ kc (arr a b) star; kc' <- expand' kc; a' <- expand' a; b' <- expand' b; return (a',b',kc') }
