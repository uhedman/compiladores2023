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
import MonadFD4 ( MonadFD4, printFD4 )
import Common ( Pos( NoPos ) )
import Subst ( close, close2 )

data Val = 
    Nat Int
  | Clos Clos

data Clos = 
    ClFun Env Name TTerm
  | ClFix Env Name Name TTerm

type Env = [(Name, Val)]

data Frame =
    FrApp Env TTerm
  | FrClos Clos
  | FrIfz Env TTerm TTerm
  | FrBOpL Env BinaryOp TTerm
  | FrBOpR Val BinaryOp
  | FrPrint String
  | FrLet Env TTerm

type Kont = [Frame]

seek :: MonadFD4 m => TTerm -> Env -> Kont -> m Val
seek _ _ _ = error "Not implemented"

evalOp :: BinaryOp -> Val -> Val -> Val
evalOp Add (Nat n) (Nat n')= Nat (n+n')
evalOp Sub (Nat n) (Nat n')= Nat (n-n')
evalOp _ _ _ = error "Binary operation with closures"

destroy :: MonadFD4 m => Val -> Kont -> m Val
destroy v (FrPrint s:k) = 
  do printFD4 s -- agregar str(v)
     destroy v k
destroy n (FrBOpL env op u:k) = seek u env (FrBOpR n op:k)
destroy n' (FrBOpR n op:k) = destroy (evalOp op n n') k
destroy (Nat 0) (FrIfz env t e:k) = seek t env k
destroy np (FrIfz env t e:k) = seek e env k
destroy (Clos c) (FrApp env t:k) = seek t env (FrClos c:k)
destroy v (FrClos (ClFun env x t):k) = seek t ((x,v):env) k
destroy v (FrClos (ClFix env f x t):k) = seek t ((f,Clos (ClFix env f x t)):(x,v):env) k
destroy v e = return v

cek :: MonadFD4 m => TTerm -> m TTerm
cek t = do t' <- seek t [] []
           case t' of
             Nat c -> return $ Const (NoPos, NatTy) (CNat c)
             Clos (ClFun e n s) -> return $ Lam (NoPos, NatTy) n NatTy (close n s) -- Wip
             Clos (ClFix e f n s) -> return $ Fix (NoPos, NatTy) f NatTy n NatTy (close2 f n s) -- Wip