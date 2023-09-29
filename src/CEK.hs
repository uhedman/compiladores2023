{-|
Module      : CEK
Description : Maquina CEK.
Copyright   : (c) Mauro Jaskelioff, Guido Martínez, 2020.
License     : GPL-3
Maintainer  : mauro@fceia.unr.edu.ar
Stability   : experimental

-}

module CEK where

import Lang
import MonadFD4 ( MonadFD4, failFD4 )
import Common ( Pos( NoPos ) )
import Subst ( close, close2 )

data Val = 
    Nat Const
  | Clos Clos

data Clos = 
    ClFun Env Name TTerm
  | ClFix Env Name Name TTerm  

type Env = [(Name, Val)]

data Frame =
    FrApp Env TTerm
  | FrClos Clos
  | FrIfz Env TTerm TTerm
  | FrBOpL Env TTerm
  | FrBOpR TTerm
  | FrPrint String
  | FrLet Env TTerm

type Kont = [Frame]

seek :: MonadFD4 m => TTerm -> Env -> Kont -> m Val
seek = failFD4 "Not implemented"

destroy :: MonadFD4 m => Val -> Kont -> m Val
destroy = failFD4 "Not implemented"

cek :: MonadFD4 m => TTerm -> m TTerm
cek t = do t' <- seek t [] []
           case t' of
             Nat c -> return $ Const (NoPos, NatTy) c
             Clos (ClFun e n s) -> return $ Lam (NoPos, NatTy) n NatTy (close n s) -- Wip
             Clos (ClFix e f n s) -> return $ Fix (NoPos, NatTy) f NatTy n NatTy (close2 f n s) -- Wip