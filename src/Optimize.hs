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
  ( optimizeDecl )
 where

import Lang
import MonadFD4
import Subst ( subst )

hasEffects :: TTerm -> Bool
hasEffects (V _ _) = False
hasEffects (Const _ _) = False
hasEffects (Lam _ _ _ (Sc1 t)) = hasEffects t
hasEffects (App _ l r) = True
hasEffects Print {} = True
hasEffects (BinaryOp _ _ l r) = hasEffects l || hasEffects r
hasEffects (Fix _ _ _ _ _ (Sc2 t)) = hasEffects t
hasEffects (IfZ _ c t e) = hasEffects c || hasEffects t || hasEffects e
hasEffects (Let _ _ _ def (Sc1 t)) = hasEffects def || hasEffects t

loop :: MonadFD4 m => Int -> TTerm -> m TTerm
loop n e = do
  if n == 0 
  then return e
  else do e' <- optimizeTerm e
          if e == e' then return e' else loop (n-1) e'

optimizeDecl :: MonadFD4 m => Decl TTerm -> m (Decl TTerm)
optimizeDecl (Decl p x t) = 
  do t' <- loop 50 t
     return $ Decl p x t'
optimizeDecl d@DeclTy {} = return d

optimizeTerm :: MonadFD4 m => TTerm -> m TTerm
-- Constant folding
optimizeTerm (BinaryOp i Add (Const _ (CNat n)) (Const _ (CNat m))) = return $ Const i (CNat (n+m))
optimizeTerm (BinaryOp _ Add (Const _ (CNat 0)) m) = return m
optimizeTerm (BinaryOp _ Add n (Const _ (CNat 0))) = return n
optimizeTerm (BinaryOp i Sub (Const _ (CNat n)) (Const _ (CNat m))) = return $ Const i (CNat (n-m))
optimizeTerm (BinaryOp _ Sub n (Const _ (CNat 0))) = return n
optimizeTerm (Let i x ty def (Sc1 c@(Const _ _))) = 
  if hasEffects def
  then do def' <- optimizeTerm def
          return $ Let i x ty def' (Sc1 c)
  else return c
-- Constant Propagation
optimizeTerm (Let _ n _ c@(Const _ _) t) = return $ subst c t
-- Recursion
optimizeTerm v@(V _ _) = return v
optimizeTerm c@(Const _ _) = return c
optimizeTerm (Lam i x ty (Sc1 t)) = 
  do t' <- optimizeTerm t
     return $ Lam i x ty (Sc1 t')
optimizeTerm (App i l r) = 
  do l' <- optimizeTerm l
     r' <- optimizeTerm r
     return $ App i l' r'
optimizeTerm (Print i str t) = 
  do t' <- optimizeTerm t
     return $ Print i str t'
optimizeTerm (BinaryOp i op l r) = 
  do l' <- optimizeTerm l
     r' <- optimizeTerm r
     return $ BinaryOp i op l' r'
optimizeTerm (Fix i x xty f fty (Sc2 t)) = 
  do t' <- optimizeTerm t
     return $ Fix i x xty f fty (Sc2 t')
optimizeTerm (IfZ i c t e) = 
  do c' <- optimizeTerm c
     t' <- optimizeTerm t
     e' <- optimizeTerm e
     return $ IfZ i c' t' e'
optimizeTerm (Let i x ty def (Sc1 t)) = 
  do def' <- optimizeTerm def
     return $ Let i x ty def' (Sc1 t)
    --  t' <- optimizeTerm t
    --  return $ Let i x ty def' (Sc1 t')