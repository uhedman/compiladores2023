{-|
Module      : Optimize
Description : Compila a bytecode. Ejecuta bytecode.
Copyright   : (c) Mauro Jaskelioff, Guido Martínez, 2020.
License     : GPL-3
Maintainer  : mauro@fceia.unr.edu.ar
Stability   : experimental

Este módulo permite compilar módulos a la Macchina. También provee
una implementación de la Macchina para ejecutar el bytecode.
-}
module Optimize
  ( optimizeDecl, optimizeTerm )
 where

import Lang
import MonadFD4
import Subst ( subst, open )
import Control.Monad.Extra ( (||^) )

hasPrint :: MonadFD4 m => TTerm -> m Bool
hasPrint (V _ (Global n)) = 
  do d <- lookupDecl n
     case d of
       Just t -> hasPrint t
       _ -> failFD4 "Global variable not assigned"
hasPrint (V _ _) = return False
hasPrint (Const _ _) = return False
hasPrint (Lam _ _ _ (Sc1 t)) = hasPrint t
hasPrint (App _ l r) = 
  do l' <- hasPrint l
     if l' then return True else hasPrint r
hasPrint Print {} = return True
hasPrint (BinaryOp _ _ l r) = hasPrint l ||^ hasPrint r
hasPrint (Fix _ _ _ _ _ (Sc2 t)) = hasPrint t
hasPrint (IfZ _ c t e) = hasPrint c ||^ hasPrint t ||^ hasPrint e
hasPrint (Let _ _ _ def (Sc1 t)) = hasPrint def ||^ hasPrint t

hasVar :: Name -> TTerm -> Bool
hasVar n (V _ (Free m)) = n == m
hasVar n (V _ _) = False
hasVar _ Const {} = False
hasVar n (Lam _ m _ (Sc1 t)) = n /= m && hasVar n t
hasVar n (App _ l r) = hasVar n l || hasVar n r
hasVar _ Print {} = False
hasVar n (BinaryOp _ _ l r) = hasVar n l || hasVar n r
hasVar n (Fix _ x _ f _ (Sc2 t)) = n /= x && n /= f && hasVar n t
hasVar n (IfZ _ c t e) = hasVar n c || hasVar n t || hasVar n e
hasVar n (Let _ m _ def (Sc1 t)) = n /= m && (hasVar n def || hasVar n t)

loop :: MonadFD4 m => Int -> TTerm -> m TTerm
loop n e = do
  if n == 0 
  then return e
  else do (b, e') <- optimizeTerm e
          if b then loop (n-1) e' else return e' 

optimizeDecl :: MonadFD4 m => Decl TTerm -> m (Decl TTerm)
optimizeDecl (Decl p x t) = 
  do t' <- loop 50 t
     return $ Decl p x t'
optimizeDecl d@DeclTy {} = return d

-- Constant folding
consFold :: MonadFD4 m => TTerm -> m (Bool, TTerm)
consFold (BinaryOp i Add (Const _ (CNat n)) (Const _ (CNat m))) = return (True, Const i (CNat (n+m)))
consFold (BinaryOp _ Add (Const _ (CNat 0)) m) = return (True, m)
consFold (BinaryOp _ Add n (Const _ (CNat 0))) = return (True, n)
consFold (BinaryOp i Sub (Const _ (CNat n)) (Const _ (CNat m))) = return (True, Const i (CNat (max (n-m) 0)))
consFold (BinaryOp _ Sub n (Const _ (CNat 0))) = return (True, n)
consFold t@(BinaryOp i Sub (Const _ (CNat 0)) n) = 
  do b <- hasPrint n
     if b then return (False, t)
          else return (True, Const i (CNat 0))
consFold t = return (False, t)

-- Dead code elimination
deadCode :: MonadFD4 m => TTerm -> m (Bool, TTerm)
deadCode l@(Let i "_" ty def t) = 
  do b <- hasPrint def
     if b 
     then return (False, l)
     else return (True, open "_" t)
deadCode l@(Let i x ty def t) = 
  do b <- hasPrint def
     if b || hasVar x (open x t) -- ineficiente
     then return (False, l)
     else return (True, open x t)
deadCode t = return (False, t)

-- Constant Propagation
constProg :: MonadFD4 m => TTerm -> m (Bool, TTerm)
constProg (Let _ _ _ c@(Const _ _) t) = return (True, subst c t)
constProg t = return (False, t)

-- Inline expansion
inlineExp :: MonadFD4 m => TTerm -> m (Bool, TTerm)
inlineExp l@(Let _ x _ Lam {} (Sc1 t)) = return (False, l) -- wip
inlineExp l@(Let _ x _ Fix {} (Sc1 t)) = return (False, l) -- wip
inlineExp l@(Let _ x _ def (Sc1 t)) = 
  do b <- hasPrint def
     if b 
     then return (False, l)
     else return (True, subst def (Sc1 t))
inlineExp t = return (False, t)

optimizeTerm :: MonadFD4 m => TTerm -> m (Bool, TTerm)
optimizeTerm v@(V _ _) = return (False, v)
optimizeTerm c@(Const _ _) = return (False, c)
optimizeTerm t@BinaryOp {} = consFold t
optimizeTerm l@(Let i x ty def t) = 
  do (b, l') <- deadCode l
     if b 
     then return (b, l')
     else do def' <- consFold def
             case def' of 
              (True, Const {}) -> constProg (Let i x ty (snd def') t)
              (False, _) -> inlineExp l
              res -> return res
optimizeTerm t = return (False, t)