module ClosureConvert where

import IR
import Lang
import Control.Monad.Writer
import Control.Monad.State
import Subst ( open, open2 )
import Data.List (nub)
import MonadFD4 (MonadFD4)

-- Closure convert y hoisting
convert :: TTerm -> StateT Int (Writer [IrDecl]) Ir
convert (V _ Bound {}) = error "No se esperaban variables ligadas" 
convert (V _ (Free n)) = return $ IrVar n
convert (V _ (Global n)) = return $ IrGlobal n
convert (Const _ c) = return $ IrConst c
convert (Lam (_,ty) x _ body) = 
  do n <- get
     modify (+1)
     let capturedVars = nub (collectFreeVars (open x body))
     let closureArgs = [(v, IrClo) | v <- capturedVars]
     let uniqueName = "__" ++ show n
     closureBody <- convert (open x body)
     tell [IrFun uniqueName (ty2ir (getCod ty)) closureArgs closureBody]
     return (IrGlobal uniqueName)
convert (App (_,ty) l r) = 
  do funcIr <- convert l
     argIr <- convert r
     return (IrCall funcIr [argIr] (ty2ir ty))
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
convert (Let _ x ty def body) = 
  do def' <- convert def
     body' <- convert (open x body)
     return $ IrLet x (ty2ir ty) def' body'

convertDecl :: Decl TTerm -> StateT Int (Writer [IrDecl]) Ir
convertDecl (Decl _ _ body) = convert body    
convertDecl DeclTy {} = error "No se soportan sinonimos de tipo" 

runCC :: MonadFD4 m => [Decl TTerm] -> m [IrDecl]
runCC decls = return $ snd $ runWriter (runStateT (mapM convertDecl decls) 0)

-- Funciones auxiliares
collectFreeVars :: TTerm -> [Name]
collectFreeVars (V _ (Free n)) = [n]
collectFreeVars (Lam _ x _ body) = collectFreeVars (open x body)
collectFreeVars (App _ l r) = collectFreeVars l ++ collectFreeVars r
collectFreeVars (BinaryOp _ _ l r) = collectFreeVars l ++ collectFreeVars r
collectFreeVars (Fix _ x _ f _ t) = collectFreeVars (open2 f x t)
collectFreeVars (IfZ _ c t e) = collectFreeVars c ++ collectFreeVars t ++ collectFreeVars e
collectFreeVars (Let _ x _ def body) = collectFreeVars def ++ collectFreeVars (open x body) 
collectFreeVars _ = []

ty2ir :: Ty -> IrTy
ty2ir NatTy = IrInt
ty2ir FunTy {} = IrFunTy

getCod :: Ty -> Ty
getCod (FunTy _ cod) = cod
getCod _ = error "Error de tipos"
