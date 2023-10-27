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
import Subst ( subst, open, open2, close2, close )

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
hasPrint (BinaryOp _ _ l r) = 
  do l' <- hasPrint l
     if l' then return True else hasPrint r
hasPrint (Fix _ _ _ _ _ (Sc2 t)) = hasPrint t
hasPrint (IfZ _ c t e) = 
  do l' <- hasPrint c
     if l' then return True 
           else do t' <- hasPrint t
                   if t' then return True
                         else hasPrint e
hasPrint (Let _ _ _ def (Sc1 t)) = 
  do l' <- hasPrint def
     if l' then return True else hasPrint t

loop :: MonadFD4 m => Int -> TTerm -> m TTerm
loop n e = do
  if n == 0 
  then return e
  else do e' <- optimizeTerm e
          if e == e' then return e' else loop (n-1) e'

optimizeDecl :: MonadFD4 m => Decl TTerm -> m (Decl TTerm)
optimizeDecl (Decl p x t) = 
  do t' <- optimizeTerm t
     return $ Decl p x t'
optimizeDecl d@DeclTy {} = return d

optimizeTerm :: MonadFD4 m => TTerm -> m TTerm
-- Constant folding
optimizeTerm (BinaryOp i Add (Const _ (CNat n)) (Const _ (CNat m))) = return $ Const i (CNat (n+m))
optimizeTerm (BinaryOp _ Add (Const _ (CNat 0)) m) = optimizeTerm m
optimizeTerm (BinaryOp _ Add n (Const _ (CNat 0))) = optimizeTerm n
optimizeTerm (BinaryOp i Sub (Const _ (CNat n)) (Const _ (CNat m))) = return $ Const i (CNat (max (n-m) 0))
optimizeTerm (BinaryOp _ Sub n (Const _ (CNat 0))) = optimizeTerm n
optimizeTerm t@(BinaryOp i Sub (Const i' (CNat 0)) n) = 
  do b <- hasPrint n
     if b then do n' <- optimizeTerm n
                  return $ BinaryOp i Sub (Const i' (CNat 0)) n'
          else return $ Const i' (CNat 0)
optimizeTerm (Let i x ty def (Sc1 c@(Const _ _))) = 
  do b <- hasPrint def
     if b then do def' <- optimizeTerm def
                  return $ Let i x ty def' (Sc1 c)
          else return c
-- Dead code elimination
optimizeTerm l@(Let i "_" ty def (Sc1 t)) = 
  do b <- hasPrint def
     if b then do def' <- optimizeTerm def
                  t' <- optimizeTerm t
                  return $ Let i "_" ty def' (Sc1 t')
          else return t
-- Constant Propagation
optimizeTerm (Let _ _ _ c@(Const _ _) t) = return $ subst c t
-- Recursion
optimizeTerm v@(V _ _) = return v
optimizeTerm c@(Const _ _) = return c
optimizeTerm (Lam i x ty t) = 
  do t' <- optimizeTerm (open x t)
     return $ Lam i x ty (close x t')
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
optimizeTerm (Fix i x xty f fty t) = 
  do t' <- optimizeTerm (open2 x f t)
     return $ Fix i x xty f fty (close2 x f t')
optimizeTerm (IfZ i c t e) = 
  do c' <- optimizeTerm c
     t' <- optimizeTerm t
     e' <- optimizeTerm e
     return $ IfZ i c' t' e'
optimizeTerm (Let i x ty def t) = 
  do def' <- optimizeTerm def
     t' <- optimizeTerm (open x t)
     return $ Let i x ty def' (Sc1 t')
