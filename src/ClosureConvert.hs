module ClosureConvert where

import IR ( Ir(..), IrDecl(IrVal, IrFun), IrTy(..) )
import Lang
    ( freeVarsTy,
      Decl(DeclTy, Decl),
      Name,
      Scope(Sc1),
      Scope2(Sc2),
      TTerm,
      Tm(Let, V, Const, Lam, App, Print, BinaryOp, Fix, IfZ),
      Ty(..),
      Var(Global, Bound, Free) )
import Control.Monad.Writer
    ( Writer, runWriter, MonadWriter(tell) )
import Control.Monad.State
    ( modify, MonadState(get), StateT(runStateT) )
import Subst ( open, open2 )
import MonadFD4 (MonadFD4, printFD4)

buildLets :: [(Name, Ty)] -> Name -> Ir -> Int -> Ir
buildLets ((x,ty):vs) clo t i  = IrLet x (ty2ir ty) (IrAccess (IrVar clo) (ty2ir ty) i) (buildLets vs clo t (i+1))
buildLets [] _ t _ = t

-- Closure convert y hoisting
convert :: TTerm -> StateT Int (Writer [IrDecl]) Ir
convert (V _ Bound {}) = error "No se esperaban variables ligadas" 
convert (V _ (Free n)) = return (IrVar n)
convert (V _ (Global n)) = return $ IrGlobal n
convert (Const _ c) = return $ IrConst c
convert (Lam (_,ty) _ xty body@(Sc1 t)) = 
  do funName <- getFreshName
     cloName <- getFreshName
     xname <- getFreshName
     body' <- convert (open xname body)
     let fvs = freeVarsTy t
     let bbody = buildLets fvs cloName body' 1
     tell [IrFun funName (ty2ir (getCod ty)) [(cloName, IrClo), (xname, ty2ir xty)] bbody]
     return (MkClosure funName (map (IrVar . fst) fvs))
convert (App (_,ty) l r) = 
  do funcIr <- convert l 
     argIr <- convert r 
     clos <- getFreshName
     return $ IrLet clos IrClo funcIr (IrCall (IrAccess (IrVar clos) IrClo 0) [IrVar clos, argIr] IrInt)
convert (Print _ s t)  = 
  do t' <- convert t 
     var <- getFreshName
     return $ IrLet var IrInt t' (IrPrint s (IrVar var))
convert (BinaryOp _ op l r)  = 
  do l' <- convert l 
     r' <- convert r 
     return $ IrBinaryOp op l' r'
convert (Fix _ _ fty _ xty body@(Sc2 t))  =
  do funName <- getFreshName
     cloName <- getFreshName
     fname <- getFreshName
     xname <- getFreshName
     body' <- convert (open2 fname xname body)
     let fvs = freeVarsTy t
     let bbody = IrLet fname (ty2ir fty) (IrVar cloName) (buildLets fvs cloName body' 1)
     tell [IrFun funName (ty2ir (getCod fty)) [(cloName, IrClo), (xname, ty2ir xty)] bbody]
     return (MkClosure funName (map (IrVar . fst) fvs))
convert (IfZ _ c t e)  = 
  do c' <- convert c 
     t' <- convert t 
     e' <- convert e 
     return $ IrIfZ c' t' e'
convert (Let _ _ ty def body)  = 
  do def' <- convert def
     xname <- getFreshName
     body' <- convert (open xname body)
     return $ IrLet xname (ty2ir ty) def' body'

convertDecl :: Decl TTerm -> StateT Int (Writer [IrDecl]) Ir
convertDecl (Decl _ x body) =
  do b <- convert body
     tell [IrVal x IrInt b]
     return b
convertDecl DeclTy {} = error "No se soportan sinonimos de tipo" 

runCC :: MonadFD4 m => [Decl TTerm] -> m [IrDecl]
runCC decls = do let ird = snd $ runWriter (runStateT (mapM convertDecl decls) 0)
                 printFD4 $ show ird
                 printFD4 $ unlines $ map show decls
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