module ClosureConvert where

import IR
import Lang
import Control.Monad.Writer
import Control.Monad.State
import Subst ( open ) --, open2 )
import MonadFD4 (MonadFD4)

-- Closure convert y hoisting
convert :: TTerm -> [(Name, Ir)] -> StateT (Name, Int) (Writer [IrDecl]) Ir
convert (V _ Bound {}) _ = error "No se esperaban variables ligadas" 
convert (V _ (Free n)) list = case lookup n list of
                                Just a -> return a
                                Nothing -> error n
convert (V _ (Global n)) _ = return $ IrGlobal n
convert (Const _ c) _ = return $ IrConst c
convert (Lam (_,ty) x xty body) list = 
  do funName <- getFunName
     cloName <- getFreshName
     let ir = IrAccess (IrVar cloName) (ty2ir xty) 0
     closureBody <- convert (open x body) ((x,ir):list)
     tell [IrFun funName (ty2ir (getCod ty)) [(funName, IrFunTy), (cloName, IrClo)] closureBody]
     return (MkClosure x [closureBody])
convert (App (_,ty) l r) list = 
  do funcIr <- convert l list
     argIr <- convert r list
     return (IrCall funcIr [funcIr, argIr] (ty2ir ty))
convert (Print _ s t) list = 
  do t' <- convert t list
     return $ IrPrint s t' 
convert (BinaryOp _ op l r) list = 
  do l' <- convert l list
     r' <- convert r list
     return $ IrBinaryOp op l' r'
convert (Fix _ x _ f ty t) list = undefined
  -- do freshName <- getFreshName
  --    closureBody <- convert (open2 f x t) list
  --    tell [IrFun freshName (ty2ir (getCod ty)) [] closureBody]
  --    return (IrGlobal freshName)
convert (IfZ _ c t e) list = 
  do c' <- convert c list
     t' <- convert t list
     e' <- convert e list
     return $ IrIfZ c' t' e'
convert (Let _ x ty def body) list = 
  do setFunName x
     def' <- convert def list 
     body' <- convert (open x body) ((x, def'):list)
     return $ IrLet x (ty2ir ty) def' body'

convertDecl :: Decl TTerm -> StateT (Name, Int) (Writer [IrDecl]) Ir
convertDecl (Decl _ x body) = do setFunName x
                                 b <- convert body []
                                 case b of
                                   MkClosure {} -> return ()
                                   _ -> do freshName <- getFreshName
                                           tell [IrVal freshName IrInt b]
                                 return b
convertDecl DeclTy {} = error "No se soportan sinonimos de tipo" 

runCC :: MonadFD4 m => [Decl TTerm] -> m [IrDecl]
runCC decls = do let ird = snd $ runWriter (runStateT (mapM convertDecl decls) ("", 0))
                --  printFD4 $ show ird
                 return ird

-- Funciones auxiliares
getFreshName :: StateT (Name, Int) (Writer [IrDecl]) Name
getFreshName = do (name, int) <- get
                  put (name, int+1)
                  return $ show int

getFunName :: StateT (Name, Int) (Writer [IrDecl]) Name
getFunName = do (name, int) <- get
                return name

setFunName :: Name -> StateT (Name, Int) (Writer [IrDecl]) ()
setFunName newName = do modify (\(_, int) -> (newName, int))

ty2ir :: Ty -> IrTy
ty2ir NatTy = IrInt
ty2ir FunTy {} = IrFunTy

getCod :: Ty -> Ty
getCod (FunTy _ cod) = cod
getCod _ = error "Error de tipos"
