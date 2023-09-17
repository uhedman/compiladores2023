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

-- | 'elab' transforma variables ligadas en índices de de Bruijn
-- en un término dado. 
elab :: STerm -> Term
elab = elab' []

elab' :: [Name] -> STerm -> Term
elab' env (SV p v) =
  -- Tenemos que ver si la variable es Global o es un nombre local
  -- En env llevamos la lista de nombres locales.
  if v `elem` env 
    then  V p (Free v)
    else V p (Global v)

elab' _ (SConst p c) = Const p c
elab' env (SLam p [] t) = elab' env t
elab' env (SLam p ((v, ty):binds) t) =
  Lam p v (sty2ty ty) (close v (elab' (v:env) (SLam p binds t)))
elab' env (SFix p (f,fty) (x,xty) binds t) = --Wip uso de p
  Fix p f (sty2ty fty) x (sty2ty xty) (close2 f x (elab' (x:f:env) (SLam p binds t)))
elab' env (SIfZ p c t e) = 
  IfZ p (elab' env c) (elab' env t) (elab' env e)
-- Operadores binarios
elab' env (SBinaryOp i o t u) = BinaryOp i o (elab' env t) (elab' env u)
-- Operador Print
elab' env (SPrint i str t) = Print i str (elab' env t)
-- Aplicaciones generales
elab' env (SApp p h a) = App p (elab' env h) (elab' env a)
elab' env (SLetLam p recBool [] (v,vty) def body) = Const p (CNat (-1)) -- Eliminar
elab' env (SLetLam p recBool [(x,xty)] (v,vty) def body) --Wip uso de p
  | recBool = elab' env (SLetVar p (v, vty) (SFix p (v, SFun xty vty) (x, xty) [] def) body)
  | otherwise = Let p v (sty2ty vty) (elab' env def) (close v (elab' (v:env) body))
elab' env (SLetLam p recBool ((x,xty):binds) (v,vty) def body) --Wip uso de p
  | recBool = elab' env (SLetLam p True [] (v, types binds vty) (SLam p binds def) body)
  | otherwise = Let p v (sty2ty vty) (elab' env def) (close v (elab' (v:env) body))
elab' env (SLetVar p (v,vty) def body) =
  Let p v (sty2ty vty) (elab' env def) (close v (elab' (v:env) body))

types :: [(Name, STy)] -> STy -> STy
types binds v = foldr f v binds
  where f (_, vty) = SFun vty

elabDecl :: Decl STerm -> Decl Term
elabDecl = fmap elab

sty2ty :: STy -> Ty
sty2ty SNatTy = NatTy
sty2ty (SFun t t') = FunTy (sty2ty t) (sty2ty t')
sty2ty (Syn name) = NatTy -- Wip necesitaria el entorno donde se uso type
