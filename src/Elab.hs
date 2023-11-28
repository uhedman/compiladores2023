{-|
Module      : Elab
Description : Elabora un término fully named a uno locally closed.
Copyright   : (c) Mauro Jaskelioff, Guido Martínez, 2020.
License     : GPL-3
Maintainer  : mauro@fceia.unr.edu.ar
Stability   : experimental

Este módulo permite elaborar términos y declaraciones para convertirlas desde
fully named (@STerm) a locally closed (@Term@)
-}

module Elab (elab, elabDecl) where

import Lang
import Subst
import MonadFD4 (MonadFD4, lookupTy, failFD4, failPosFD4)

-- | 'elab' transforma variables ligadas en índices de de Bruijn
-- en un término dado. 
elab :: MonadFD4 m => STerm -> m Term
elab = elab' []

elab' :: MonadFD4 m => [Name] -> STerm -> m Term
elab' env (SV p v) =
  -- Tenemos que ver si la variable es Global o es un nombre local
  -- En env llevamos la lista de nombres locales.
  if v `elem` env 
    then return $ V p (Free v)
    else return $ V p (Global v)

elab' _ (SConst p c) = return $ Const p c
elab' env (SLam p [] t) = failPosFD4 p "Funcion sin argumentos"
elab' env (SLam p [(v, ty)] t) = 
  do ty' <- sty2ty ty
     e' <- elab' (v:env) t
     return $ Lam p v ty' (close v e')
elab' env (SLam p ((v, ty):binds) t) = 
  do ty' <- sty2ty ty
     e' <- elab' (v:env) (SLam p binds t)
     return $ Lam p v ty' (close v e')
elab' env (SFix p (f,fty) (x,xty) [] t) =
  do fty' <- sty2ty fty
     xty' <- sty2ty xty
     e' <- elab' (x:f:env) t
     return $ Fix p f fty' x xty' (close2 f x e')
elab' env (SFix p (f,fty) (x,xty) binds t) =
  do fty' <- sty2ty fty
     xty' <- sty2ty xty
     e' <- elab' (x:f:env) (SLam p binds t)
     return $ Fix p f fty' x xty' (close2 f x e')
elab' env (SIfZ p c t e) = 
  do c' <- elab' env c
     t' <- elab' env t
     e' <- elab' env e
     return $ IfZ p c' t' e'
-- Operadores binarios
elab' env (SBinaryOp i o t u) = 
  do t' <- elab' env t
     u' <- elab' env u
     return $ BinaryOp i o t' u'
-- Operador Print
elab' env (SPrint i str t) = 
  do t' <- elab' env t
     return $ Print i str t'
-- Aplicaciones generales
elab' env (SApp p h a) = 
  do h' <- elab' env h
     a' <- elab' env a
     return $ App p h' a'
elab' env (SLetVar p (v,vty) def body) =
  do vty' <- sty2ty vty
     def' <- elab' env def
     body' <- elab' (v:env) body
     return $ Let p v vty' def' (close v body')
elab' env (SLetLam p [] (v,vty) def body) = failPosFD4 p "Let sin argumentos"
elab' env (SLetFix p [] (v,vty) def body) = failPosFD4 p "Let sin argumentos"
elab' env (SLetLam p [(x,xty)] (v,vty) def body) = 
  elab' env $ SLetVar p (v, SFun xty vty) (SLam p [(x,xty)] def) body
elab' env (SLetFix p [(x,xty)] (v,vty) def body) =
  elab' env (SLetVar p (v, vty) (SFix p (v, SFun xty vty) (x, xty) [] def) body)
elab' env (SLetLam p ((x,xty):binds) (v,vty) def body) =
  elab' env $ SLetVar p (v, types ((x,xty):binds) vty) def body
elab' env (SLetFix p ((x,xty):binds) (v,vty) def body) = 
  elab' env (SLetFix p [(x,xty)] (v, types binds vty) (SLam p binds def) body)

elabDecl :: MonadFD4 m => SDecl STerm -> m (Decl Term)
elabDecl (SDeclTy p n ty) = 
  do ty' <- sty2ty ty
     return $ DeclTy p n ty'
elabDecl (SDeclVar p n ty body) = 
  do body' <- elab body
     return $ Decl p n body'
elabDecl (SDeclLam p n [] ty body) = failPosFD4 p "Declaracion de funcion sin argumentos"
elabDecl (SDeclFix p n [] ty body) = failPosFD4 p "Declaracion de funcion sin argumentos"
elabDecl (SDeclLam p n args ty body) = 
  elabDecl $ SDeclVar p n (types args ty) (SLam p args body)
elabDecl (SDeclFix p n [(x, xty)] ty body) = 
  elabDecl $ SDeclVar p n (SFun xty ty) (SFix p (n, SFun xty ty) (x, xty) [] body)
elabDecl (SDeclFix p n args ty body) = 
  elabDecl $ SDeclFix p n [head args] (types (tail args) ty) (SLam p (tail args) body)

-- Funciones auxiliares

types :: [(Name, STy)] -> STy -> STy
types binds v = foldr f v binds
  where f (_, vty) = SFun vty

sty2ty :: MonadFD4 m => STy -> m Ty
sty2ty SNatTy = return NatTy
sty2ty (SFun t1 t2) = 
  do t1' <- sty2ty t1
     t2' <- sty2ty t2
     return $ FunTy t1' t2'
sty2ty (Syn name) = 
  do res <- lookupTy name 
     case res of
       Nothing -> failFD4 $ "Sinonimo de tipo no reconocido: " ++ name
       Just ty -> return ty 
