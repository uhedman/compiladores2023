module Optimize
  ( optimizeDecl, optimizeTerm )
 where

import Lang
    ( BinaryOp(Sub, Add),
      Const(CNat),
      Decl(DeclTy, Decl),
      Scope(Sc1),
      Scope2(Sc2),
      TTerm,
      Tm(..),
      Var(..) )
import MonadFD4 ( lookupDecl, MonadFD4, failPosFD4 )
import Subst
import Control.Monad.Extra ( (||^) )
import PPrint (ppName)
import Common (Pos(NoPos))

loop :: MonadFD4 m => Int -> TTerm -> m TTerm
loop n e = do
  if n == 0 
  then return e
  else do (b, e') <- optimizeTerm e
          if b then loop (n-1) e' else return e' 

optimizeDecl :: MonadFD4 m => Decl TTerm -> m (Decl TTerm)
optimizeDecl (Decl p x t) = 
  do t' <- loop 50 t
     return $ Decl p x t'
optimizeDecl d@DeclTy {} = return d

-- Constant folding
consFold :: MonadFD4 m => TTerm -> m (Bool, TTerm)
consFold (BinaryOp i Add (Const _ (CNat n)) (Const _ (CNat m))) = return (True, Const i (CNat (n+m)))
consFold (BinaryOp _ Add (Const _ (CNat 0)) m) = return (True, m)
consFold (BinaryOp _ Add n (Const _ (CNat 0))) = return (True, n)
consFold (BinaryOp i Sub (Const _ (CNat n)) (Const _ (CNat m))) = return (True, Const i (CNat (max (n-m) 0)))
consFold (BinaryOp _ Sub n (Const _ (CNat 0))) = return (True, n)
consFold t@(BinaryOp i Sub (Const _ (CNat 0)) m) = 
  do b <- hasPrint m
     if b then return (False, t)
          else return (True, Const i (CNat 0))
consFold (BinaryOp i op n m) = 
  do (bl, n') <- optimizeTerm n
     (br, m') <- optimizeTerm m
     return (bl || br, BinaryOp i op n' m')
consFold t = return (False, t)

-- Dead code elimination
deadCode :: MonadFD4 m => TTerm -> m (Bool, TTerm)
deadCode l@(Let _ x _ def (Sc1 t)) = 
  do b <- hasPrint def
     if b || hasVar 0 t
     then return (False, l)
     else return (True, open x (Sc1 t))
deadCode (IfZ _ (Const _ (CNat n)) t e) = 
  if n == 0 then return (True, t)
            else return (True, e)
deadCode t = return (False, t)

-- Constant Propagation
constProp :: MonadFD4 m => TTerm -> m (Bool, TTerm)
constProp (Let _ _ _ c@(Const _ _) t) = return (True, subst c t)
constProp t = return (False, t)

optimizeTerm :: MonadFD4 m => TTerm -> m (Bool, TTerm)
optimizeTerm v@(V _ (Global l)) = 
  do d <- lookupDecl l
     case d of
       Just l' -> return (True, l')
       Nothing -> return (False, v)
optimizeTerm v@V {} = return (False, v)
optimizeTerm c@Const {} = return (False, c)
optimizeTerm (Lam i x ty t) = 
  do (b, t') <- optimizeTerm (open x t)
     if b 
     then return (True, Lam i x ty (close x t'))
     else return (False, Lam i x ty t)
optimizeTerm t@(App i (V i' (Global l)) r) = 
  do d <- lookupDecl l
     case d of
       Just l' -> return (True, App i l' r)
       Nothing -> return (False, t)
optimizeTerm (App _ (Lam _ x ty t) r) = 
  case r of 
    V {} -> return (True, subst r t)
    Const {} -> return (True, subst r t)
    _ -> return (True, Let (NoPos, ty) x ty r t)
optimizeTerm (App i l r) = 
  do (bl, l') <- optimizeTerm l
     (br, r') <- optimizeTerm r
     return (bl || br, App i l' r')
optimizeTerm (Print i s t) = 
  do (b, t') <- optimizeTerm t
     return (b, Print i s t')
optimizeTerm t@BinaryOp {} = consFold t
optimizeTerm (Fix i x xty f fty s) = 
  do (b, t') <- optimizeTerm (open2 f x s)
     if b
     then return (True, Fix i x xty f fty (close2 f x t'))
     else return (False, Fix i x xty f fty s)
optimizeTerm z@(IfZ i (Const {}) t e) = deadCode z
optimizeTerm (IfZ i c t e) = 
  do (bc, c') <- optimizeTerm c
     (bt, t') <- optimizeTerm t
     (be, e') <- optimizeTerm e
     return (bc || bt || be, IfZ i c' t' e')
optimizeTerm l@(Let i x ty def t) = do
  (bd, ld) <- deadCode l
  if bd
    then return (True, ld)
    else do
      (bf1, defFold) <- consFold def
      if bf1
        then return (True, Let i x ty defFold t)
        else do
          (bf2, bodyFold) <- consFold (open x t)
          if bf2
            then return (True, Let i x ty def (close x bodyFold))
            else constProp l

-- Funciones auxiliares

-- | Busca un print en el término t
hasPrint :: MonadFD4 m => TTerm -> m Bool
hasPrint (V (p, _) (Global n)) = 
  do d <- lookupDecl n
     case d of
       Just t -> hasPrint t
       Nothing -> failPosFD4 p $ "Error de ejecución: variable no declarada: " ++ ppName n
hasPrint (V _ _) = return False
hasPrint (Const _ _) = return False
hasPrint (Lam _ _ _ (Sc1 t)) = hasPrint t
hasPrint (App _ l r) = 
  do l' <- hasPrint l
     if l' then return True else hasPrint r
hasPrint Print {} = return True
hasPrint (BinaryOp _ _ l r) = hasPrint l ||^ hasPrint r
hasPrint (Fix _ _ _ _ _ (Sc2 t)) = hasPrint t
hasPrint (IfZ _ c t e) = hasPrint c ||^ hasPrint t ||^ hasPrint e
hasPrint (Let _ _ _ def (Sc1 t)) = hasPrint def ||^ hasPrint t

-- | Busca la variable Bound n en el término t
hasVar :: Int -> TTerm -> Bool
hasVar n (V _ (Bound i)) = n == i
hasVar _ (V _ _) = False 
hasVar n (Lam _ _ _ (Sc1 t)) = hasVar (n+1) t
hasVar n (App p l r) = hasVar n l || hasVar n r
hasVar n (Fix p f fty x xty (Sc2 t)) = hasVar (n+2) t
hasVar n (IfZ p c t e) = hasVar n c || hasVar n t || hasVar n e
hasVar n Const {} = False
hasVar n (Print p str t) = hasVar n t
hasVar n (BinaryOp p op t u) = hasVar n t || hasVar n u
hasVar n (Let p v vty m (Sc1 o)) = hasVar n m || hasVar (n+1) o

-- | Cuenta las repeticiones de la variable Bound n en el término t
countVar :: Int -> TTerm -> Int
countVar n (V _ (Bound i)) = if n == i then 1 else 0
countVar n V {} = 0 
countVar n (Lam _ _ _ (Sc1 t)) = countVar (n+1) t
countVar n (App p l r) = countVar n l + countVar n r
countVar n (Fix p f fty x xty (Sc2 t)) = countVar (n+2) t
countVar n (IfZ p c t e) = countVar n c + countVar n t + countVar n e
countVar n Const {} = 0
countVar n (Print p str t) = countVar n t
countVar n (BinaryOp p op t u) = countVar n t + countVar n u
countVar n (Let p v vty m (Sc1 o)) = countVar n m + countVar (n+1) o