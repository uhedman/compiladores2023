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
import Subst ( subst, close )

hasPrint :: TTerm -> Bool
hasPrint (V _ _) = False
hasPrint (Const _ _) = False
hasPrint (Lam _ _ _ (Sc1 t)) = hasPrint t
hasPrint (App _ l r) = hasPrint l || hasPrint r
hasPrint Print {} = True
hasPrint (BinaryOp _ _ l r) = hasPrint l || hasPrint r
hasPrint (Fix _ _ _ _ _ (Sc2 t)) = hasPrint t
hasPrint (IfZ _ c t e) = hasPrint c || hasPrint t || hasPrint e
hasPrint (Let _ _ _ def (Sc1 t)) = hasPrint def || hasPrint t

loop :: MonadFD4 m => Int -> TTerm -> m TTerm
loop n e = do
  if n == 0 
  then return e
  else do e' <- optimizeTerm e
          loop (n-1) e'

optimizeDecl :: MonadFD4 m => Decl TTerm -> m (Decl TTerm)
optimizeDecl (Decl p x t) = 
  do t' <- optimizeTerm t
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
  if hasPrint def
  then do def' <- optimizeTerm def
          return $ Let i x ty def' (Sc1 c)
  else return c
-- Constant Propagation
optimizeTerm (Let _ n _ c@(Const _ _) (Sc1 t)) = return $ subst c (close n t)
-- Propagation
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
     t' <- optimizeTerm t
     return $ Let i x ty def' (Sc1 t')
