-- vim: ts=2: sw=2: expandtab: ai:

import MicroKanren
import ExampleMember

import Control.Applicative
import Control.Monad

import Debug.Trace (trace)

a_var = A "var"
a_app = A "app"
a_lam = A "lam"
a_let = A "let"
a_arr = A "arr"
a_o = A "o"

a_mono = A "mono"
a_poly = A "poly"

mono t = L [a_mono, t]
poly c t = L [a_poly, c, t]

var x = L [a_var, x]
app t1 t2 = L [a_app, t1, t2]
lam x t = L [a_lam, x, t]
let_ x t0 t = L [a_let, x, t0, t]
arr a b = L [a_arr, a, b]

star = L [a_o]

instKi ksch k =
  ksch `eq` mono k
  <|>
  ( fresh $ \(kc,k1) -> do { ksch `eq` poly kc k1
                           ; copy_term (poly kc k1) (poly kc k)
                           ; return () }
  )

instTy kc tsch t =
  do { tsch `eq` mono t; return [] }
  <|>
  ( fresh $ \(c,t1) -> do { tsch `eq` poly c t1
                          ; s <- copy_term (poly c t1) (poly c t)
                          ; ks <- sequence [newVar | _ <- s]
                          ; return $ concat -- new tyvars must be the same kind
                              [ [ L[A"kind",kc,V v1,V k]   -- kind(kc,v1,k)
                                , L[A"kind",kc,V v2,V k] ] -- kind(kc,v2,k)
                              | ((v1,v2),k) <- zip s ks ]
                          }
  )

kind_ kc t k =
  -- kind(KC, var(X), K) :- first(X:K1, KC) instKi(K1, K).
  ( fresh $ \(x,ksch) -> do{ t `eq` var x
                           ; first x ksch kc
                           ; instKi ksch k } )
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
  -- type(KC,C, var(X), Ty) :- first(X:T, C), instTy(KC,T,Ty).
  ( fresh $ \(x,tsch) -> do{ tm `eq` var x
                           ; first x tsch ctx;
                           ; instTy kc tsch ty } )
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
  ( fresh $ \(x,tx,e,te) ->
      do{ tm `eq` lam x e
        ; ty `eq` arr tx te
        ; gs <- type_ kc (cons (pair x (mono tx)) ctx) e te
        ; return (L[A"kind",kc,arr tx te,star] : gs)
        } )
  <|>
  -- type(KC, C, let(X,E0,E), Ty) :- type(KC, C,E0,Tx),
  --                                 type(KC, [poly(X:Tx)|C], E, Ty).
  ( fresh $ \(x,tm0,tx,e) ->
      do{ tm `eq` let_ x tm0 e
        ; gs1 <- type_ kc ctx tm0 tx
        ; gs2 <- type_ kc (cons (pair x (poly ctx tx)) ctx) e ty
        ; return $ gs1++gs2
        } )

------------------------

type__ kc ctx tm ty = do
  gs <- type_ kc ctx tm ty
  ty_ <- expand' ty
  gs_ <- mapM expand' gs
  let vs = usort [x | x <-concatMap fv (ty_:[ty | L[_,_,ty,_]<- gs_])]
  conjs [V x `eq` var(A $ "_"++show x) | x <- vs]
  xks <- sequence [(,) <$> pure x <*> newVar | x <- vs]
  let monokc = [pair (A $ "_"++show x) (mono (V k)) | (x,k) <- xks]
  gs_ <- mapM expand' gs
  conjs [ fresh $ \kc0 -> do kctx `eq` (foldr cons kc0 monokc)
                             kind_ kctx t k
        | L[A"kind",kctx,t,k] <- gs_]

ex1 = tst $ fresh $ \(kc,ty) ->
  do type__ kc nil (lam x $ var x) ty
     (,) <$> expand' ty <*> expand' kc
  where x = A "x"

ex2 = tst $ fresh $ \(kc,ty) ->
  do type__ kc nil (lam x $ lam y $ var x) ty
     (,) <$> expand' ty <*> expand' kc
  where (x,y) = (A"x",A"y")


ex3 = tst $ fresh $ \(kc,ty) ->
  do type__ kc nil (lam x $ lam y $ var y) ty
     (,) <$> expand' ty <*> expand' kc
  where (x,y) = (A"x",A"y")


ex10 = let (a,b) = (V(-1),V(-2)) in tst $ fresh $ \kc -> do{ kind_ kc (arr a b) star; kc' <- expand' kc; a' <- expand' a; b' <- expand' b; return (a',b',kc') }

