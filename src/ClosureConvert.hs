module ClosureConvert where

import IR
import Lang
import Control.Monad.Writer
import Control.Monad.State
import Subst ( open, open2 )
import MonadFD4 (MonadFD4)

-- Closure convert y hoisting
convert :: TTerm -> [Name] -> StateT Int (Writer [IrDecl]) Ir
convert (V _ Bound {}) _ = error "No se esperaban variables ligadas" 
convert (V _ (Free n)) list = return (IrVar n)
convert (V _ (Global n)) _ = return $ IrGlobal n
convert (Const _ c) _ = return $ IrConst c
convert (Lam (_,ty) x xty body) list = 
  do funName <- getFreshName
     cloName <- getFreshName
     closureBody <- convert (open x body) list
     tell [IrFun funName (ty2ir (getCod ty)) [(cloName, IrClo), (x, ty2ir xty)] closureBody]
     return (MkClosure funName (map IrVar list))
convert (App (_,ty) l r) list = 
  do funcIr <- convert l list
     argIr <- convert r list
     return (IrCall (IrAccess funcIr IrFunTy 0) [funcIr, argIr] (ty2ir ty))
convert (Print _ s t) list = 
  do t' <- convert t list
     return $ IrPrint s t' 
convert (BinaryOp _ op l r) list = 
  do l' <- convert l list
     r' <- convert r list
     return $ IrBinaryOp op l' r'
convert (Fix _ x xty f fty t) list = 
  do funName <- getFreshName
     cloName <- getFreshName
     closureBody <- convert (open2 f x t) list
     tell [IrFun funName (ty2ir (getCod fty)) [(cloName, IrClo), (x, ty2ir xty)] closureBody]
     return (MkClosure funName (map IrVar list))
convert (IfZ _ c t e) list = 
  do c' <- convert c list
     t' <- convert t list
     e' <- convert e list
     return $ IrIfZ c' t' e'
convert (Let _ x ty def body) list = 
  do def' <- convert def list 
     body' <- convert (open x body) (x:list)
     return $ IrLet x (ty2ir ty) def' body'

convertDecl :: Decl TTerm -> StateT Int (Writer [IrDecl]) Ir
convertDecl (Decl _ x body) = 
  do b <- convert body []
     case b of
       (MkClosure _ args) -> 
          do cloName <- getFreshName
             let cod = getCod (getTy body)
             let dom = getDom (getTy body)
             tell [IrFun x (ty2ir cod) [(cloName, IrClo), (x, ty2ir dom)] b]
       _ -> 
          do tell [IrVal x IrInt b]
     return b
convertDecl DeclTy {} = error "No se soportan sinonimos de tipo" 

runCC :: MonadFD4 m => [Decl TTerm] -> m [IrDecl]
runCC decls = do let ird = snd $ runWriter (runStateT (mapM convertDecl decls) 0)
                --  printFD4 $ show ird
                 return ird

-- Funciones auxiliares
getFreshName :: StateT Int (Writer [IrDecl]) Name
getFreshName = do int <- get
                  modify (+1)
                  return $ show int

ty2ir :: Ty -> IrTy
ty2ir NatTy = IrInt
ty2ir FunTy {} = IrFunTy

getDom :: Ty -> Ty
getDom (FunTy dom _) = dom
getDom _ = error "Error de tipos"

getCod :: Ty -> Ty
getCod (FunTy _ cod) = cod
getCod _ = error "Error de tipos"
