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
import MonadFD4 ( MonadFD4, printFD4, failFD4, lookupDecl )
import Common ( Pos( NoPos ) )
import Subst ( close, close2, open, open2)

data Val = 
    Nat Int
  | Clos Clos

data Clos = 
    ClFun Env Name TTerm
  | ClFix Env Name Name TTerm

type Env = [Val]

data Frame =
    FrApp Env TTerm
  | FrClos Clos
  | FrIfz Env TTerm TTerm
  | FrBOpL Env BinaryOp TTerm
  | FrBOpR Val BinaryOp
  | FrPrint String
  | FrLet Env Name TTerm

type Kont = [Frame]

nth :: Int -> Env -> Maybe Val
nth _ [] = Nothing
nth 0 (v:env) = Just v
nth n (_:env) = nth (n-1) env

seek :: MonadFD4 m => TTerm -> Env -> Kont -> m Val
seek (Print _ s t) env k = seek t env (FrPrint s:k)
seek (BinaryOp _ op t u) env k = seek t env (FrBOpL env op u:k)
seek (IfZ _ c t e) env k = seek c env (FrIfz env t e:k)
seek (App _ t u) env k = seek t env (FrApp env u:k)
seek (V _ (Free n)) env k = failFD4 "Free variable when using de Bruijn indexes"
seek (V _ (Bound i)) env k = 
  case nth i env of
    Nothing -> failFD4 "Variable not found"
    Just v -> destroy v k
seek (V _ (Global n)) env k = 
  do res <- lookupDecl n
     case res of
       Nothing -> failFD4 "Variable not found"
       Just v -> seek v env k
seek (Const _ (CNat n)) env k = destroy (Nat n) k
seek (Lam _ x _ t) env k = 
  destroy (Clos (ClFun env x (open x t))) k
seek (Fix _ f _ x _ t) env k = 
  destroy (Clos (ClFix env f x (open2 f x t))) k
seek (Let _ x _ s t) env k = 
  seek s env (FrLet env x (open x t):k)

evalOp :: BinaryOp -> Val -> Val -> Val
evalOp Add (Nat n) (Nat n')= Nat (n+n')
evalOp Sub (Nat n) (Nat n')= Nat (n-n')
evalOp _ _ _ = error "Binary operation with closures"

destroy :: MonadFD4 m => Val -> Kont -> m Val
destroy v (FrPrint s:k) = 
  do printFD4 s -- agregar str(v)
     destroy v k
destroy (Nat n) (FrBOpL env op u:k) = seek u env (FrBOpR (Nat n) op:k)
destroy (Nat n') (FrBOpR (Nat n) op:k) = destroy (evalOp op (Nat n) (Nat n')) k
destroy (Nat 0) (FrIfz env t e:k) = seek t env k
destroy (Nat np) (FrIfz env t e:k) = seek e env k
destroy (Clos c) (FrApp env t:k) = seek t env (FrClos c:k)
destroy v (FrClos (ClFun env x t):k) = seek t (v:env) k
destroy v (FrClos (ClFix env f x t):k) = seek t (Clos (ClFix env f x t):v:env) k
destroy v (FrLet env x t:k) = seek t (v:env) k
destroy v [] = return v
destroy _ _ = failFD4 "Bad args in destroy"

cek :: MonadFD4 m => TTerm -> m TTerm
cek t = do t' <- seek t [] []
           case t' of
             Nat c -> return $ Const (NoPos, NatTy) (CNat c)
             Clos (ClFun e n s) -> return $ Lam (NoPos, NatTy) n NatTy (close n s) -- Wip
             Clos (ClFix e f n s) -> return $ Fix (NoPos, NatTy) f NatTy n NatTy (close2 f n s) -- Wip