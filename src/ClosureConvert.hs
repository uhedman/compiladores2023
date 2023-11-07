module ClosureConvert where

import IR
import Lang
import Control.Monad.Writer
import Control.Monad.State
import Subst ( open )

convert :: Term -> StateT Int (Writer [IrDecl]) Ir
convert (V _ Bound {}) = error "No se esperaban variables ligadas" 
convert (V _ (Free n)) = return $ IrVar n
convert (V _ (Global n)) = return $ IrGlobal n
convert (Const _ c) = return $ IrConst c
convert (Lam _ x ty s) = -- wip
  do t <- convert (open x s)
     return $ IrCall t [] IrInt
convert (App _ f x) = -- wip
  do f' <- convert f
     x' <- convert x
     n <- get
     put (n+1)
     return $ IrLet ("__" ++ show n) IrClo f' (IrAccess (MkClosure "clos" [x']) IrInt 0)
convert (Print _ s t) = 
  do t' <- convert t
     return $ IrPrint s t' 
convert (BinaryOp _ op l r) = 
  do l' <- convert l
     r' <- convert r
     return $ IrBinaryOp op l' r'
convert Fix {} = undefined 
convert (IfZ _ c t e) = 
  do c' <- convert c
     t' <- convert t
     e' <- convert e
     return $ IrIfZ c' t' e'
convert Let {} = undefined