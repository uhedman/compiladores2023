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
import MonadFD4 ( MonadFD4, printFD4, failFD4, failPosFD4, lookupDecl )
import Common ( Pos )
import Subst ( close, close2, open, open2)
import PPrint ( pp )

data Val = 
    Nat (Pos, Ty) Int
  | Clos Clos
  deriving Show

data Clos = 
    ClFun (Pos, Ty) Env Name Ty TTerm
  | ClFix (Pos, Ty) Env Name Ty Name Ty TTerm
  deriving Show

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
seek (V (p,_) (Free n)) env k = failPosFD4 p "Free variable when using de Bruijn indexes"
seek (V (p,_) (Bound i)) env k = 
  case nth i env of
    Nothing -> failPosFD4 p "Variable not found"
    Just v -> destroy v k
seek (V (p,_) (Global n)) env k = 
  do res <- lookupDecl n
     case res of
       Nothing -> failPosFD4 p  "Variable not found"
       Just v -> seek v env k
seek (Const i (CNat n)) env k = destroy (Nat i n) k
seek (Lam i x xty t) env k = 
  destroy (Clos (ClFun i env x xty (open x t))) k
seek (Fix i f fty x xty t) env k = 
  destroy (Clos (ClFix i env f fty x xty (open2 f x t))) k
seek (Let _ x _ s t) env k = 
  seek s env (FrLet env x (open x t):k)

val2string :: MonadFD4 m => Val -> m String
val2string (Nat i n) = return $ show n
val2string (Clos (ClFun i env x xty t)) = pp t
val2string (Clos (ClFix i env f fty x xty t)) = pp t

val2tterm :: Val -> TTerm
val2tterm (Nat i n) = Const i (CNat n)
val2tterm (Clos (ClFun i env x xty t)) = Lam i x xty (close x t) -- sust en t
val2tterm (Clos (ClFix i env f fty x xty t)) = Fix i f fty x xty (close2 f x t) -- sust en t

evalOp :: BinaryOp -> Val -> Val -> Val
evalOp Add (Nat i n) (Nat i' n') = Nat i (n+n')
evalOp Sub (Nat i n) (Nat i' n') = Nat i (n-n')
evalOp _ _ _ = error "Binary operation with closures"

destroy :: MonadFD4 m => Val -> Kont -> m Val
destroy v (FrPrint s:k) = 
  do vs <- val2string v
     printFD4 $ s ++ vs
     destroy v k
destroy (Nat i n) (FrBOpL env op u:k) = seek u env (FrBOpR (Nat i n) op:k)
destroy (Nat i' n') (FrBOpR (Nat i n) op:k) = destroy (evalOp op (Nat i n) (Nat i' n')) k
destroy (Nat i 0) (FrIfz env t e:k) = seek t env k
destroy (Nat i np) (FrIfz env t e:k) = seek e env k
destroy (Clos c) (FrApp env t:k) = seek t env (FrClos c:k)
destroy v (FrClos (ClFun i env x xty t):k) = seek t (v:env) k
destroy v (FrClos (ClFix i env f fty x xty t):k) = seek t (Clos (ClFix i env f fty x xty t):v:env) k
destroy v (FrLet env x t:k) = seek t (v:env) k
destroy v [] = return v
destroy _ _ = failFD4 "Bad args in destroy"

evalCEK :: MonadFD4 m => TTerm -> m TTerm
evalCEK t = do t' <- seek t [] []
               return $ val2tterm t'