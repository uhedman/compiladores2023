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
    ( BinaryOp(..),
      Const(CNat),
      Name,
      Scope(Sc1),
      Scope2(Sc2),
      TTerm,
      Tm(Fix, Print, BinaryOp, IfZ, App, V, Let, Const, Lam),
      Ty (..),
      Var(Global, Free, Bound) )
import MonadFD4
    ( failFD4, failPosFD4, lookupDecl, printFD4, MonadFD4, addStep, addDebug )
import Common ( Pos )
import Subst ( close, close2 )
import PPrint ( pp )

-- Lenguaje de valores y marcos

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
  | FrLet Env TTerm
  deriving Show

type Kont = [Frame]

-- Funciones principales

evalCEK :: MonadFD4 m => TTerm -> m TTerm
evalCEK t = do 
              --  printFD4 $ "Evaluando: " ++ show t
               t' <- seek t [] []
               return $ val2tterm t'

seek :: MonadFD4 m => TTerm -> Env -> Kont -> m Val
seek t env k = do
  addStep
  addDebug $ "seek: term = " ++ show t ++ "\nenv = " ++ show env ++ "\nkont = " ++ show k
  case t of
    Print _ s t' -> seek t' env (FrPrint s:k)
    BinaryOp _ op t' u -> seek t' env (FrBOpL env op u:k)
    IfZ _ c t' e -> seek c env (FrIfz env t' e:k)
    App _ t' u -> seek t' env (FrApp env u:k)
    V (p,_) (Free n) -> failPosFD4 p "Variable libre deberia ser indice de De Bruijn"
    V (p,_) (Bound i) ->
      case nth i env of
        Nothing -> failPosFD4 p $ "Variable local no encontrada:\n term = " ++ show t ++ "\nenv = " ++ show env ++ "\nkont = " ++ show k
        Just v -> destroy v k
    V (p,_) (Global n) -> do
      res <- lookupDecl n
      case res of
        Nothing -> failPosFD4 p "Variable global no encontrada"
        Just v -> seek v env k
    Const i (CNat n) -> destroy (Nat i n) k
    Lam i x xty (Sc1 t') -> destroy (Clos (ClFun i env x xty t')) k
    Fix i f fty x xty (Sc2 t') -> destroy (Clos (ClFix i env f fty x xty t')) k
    Let i x xty s (Sc1 t') -> seek s env (FrLet env t':k)

destroy :: MonadFD4 m => Val -> Kont -> m Val
destroy v k = do
  addStep
  addDebug $ "destroy: val = " ++ show v ++ "\nkont = " ++ show k
  case (v, k) of
    (_, FrPrint s:k') -> do
      vs <- val2string v
      printFD4 $ s ++ vs
      destroy v k'
    (Nat i n, FrBOpL env op u:k') -> seek u env (FrBOpR (Nat i n) op:k')
    (Nat i' n', FrBOpR (Nat i n) op:k') -> destroy (evalOp op (Nat i n) (Nat i' n')) k'
    (Nat _ 0, FrIfz env t' _:k') -> seek t' env k'
    (Nat _ np, FrIfz env _ e:k') -> seek e env k'
    (Clos c, FrApp env t:k') -> seek t env (FrClos c:k')
    (v', FrClos (ClFun i env x xty t):k') -> seek t (v':env) k'
    (v', FrClos (ClFix i env f fty x xty t):k') -> seek t (v':Clos (ClFix i env f fty x xty t):env) k'
    (v', FrLet env t:k') -> seek t (v':env) k'
    (v', []) -> return v'
    _ -> failFD4 "Argumentos invalidos en destroy"

-- Funciones auxiliares

nth :: Int -> Env -> Maybe Val
nth _ [] = Nothing
nth 0 (v:env) = Just v
nth n (_:env) = nth (n-1) env

val2string :: MonadFD4 m => Val -> m String
val2string (Nat i n) = return $ show n
val2string t = pp (val2tterm t)

val2tterm :: Val -> TTerm
val2tterm (Nat i n) = Const i (CNat n)
val2tterm (Clos (ClFun i env x xty t)) =
  rebuildEnv i env (Lam i x xty (close x t))
val2tterm (Clos (ClFix i env f fty x xty t)) =
  rebuildEnv i env (Fix i f fty x xty (close2 f x t))

rebuildEnv :: (Pos, Ty) -> [Val] -> TTerm -> TTerm
rebuildEnv _ [] body = body
rebuildEnv i (v:vs) body =
  rebuildEnv i vs (Let i "_" NatTy (val2tterm v) (Sc1 body))

evalOp :: BinaryOp -> Val -> Val -> Val
evalOp Add (Nat i n) (Nat i' n') = Nat i (n+n')
evalOp Sub (Nat i n) (Nat i' n') = Nat i (max 0 (n - n'))
evalOp _ _ _ = error "Operacion binaria con clausuras"