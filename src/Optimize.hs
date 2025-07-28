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
      Tm(Let, V, Lam, App, Fix, IfZ, Const, Print, BinaryOp),
      Var(Bound, Global) )
import MonadFD4 ( failFD4, lookupDecl, MonadFD4 )
import Subst ( subst, open, close, open2, close2 )
import Control.Monad.Extra ( (||^) )

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
consFold t@(BinaryOp i Sub (Const _ (CNat 0)) n) = 
  do b <- hasPrint n
     if b then return (False, t)
          else return (True, Const i (CNat 0))
consFold (BinaryOp i op n m) = 
  do (bl, n') <- optimizeTerm n
     (br, m') <- optimizeTerm m
     return (bl || br, BinaryOp i op n' m')
consFold t = return (False, t)

-- Dead code elimination
deadCode :: MonadFD4 m => TTerm -> m (Bool, TTerm)
deadCode l@(Let _ "_" _ def t) = 
  do b <- hasPrint def
     if b 
     then return (False, l)
     else return (True, open "_" t)
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
constProg :: MonadFD4 m => TTerm -> m (Bool, TTerm)
constProg (Let _ _ _ c@(Const _ _) t) = return (True, subst c t)
constProg t = return (False, t)

-- Inline expansion
inlineExp :: MonadFD4 m => TTerm -> m (Bool, TTerm)
inlineExp l@(Let _ _ _ Lam {} _) = return (False, l)
inlineExp l@(Let _ _ _ Fix {} _) = return (False, l)
inlineExp l@(Let _ _ _ def body) = 
  do b <- hasPrint def
     if b 
     then return (False, l)
     else return (True, subst def body)
inlineExp t = return (False, t)

optimizeTerm :: MonadFD4 m => TTerm -> m (Bool, TTerm)
optimizeTerm v@V {} = return (False, v)
optimizeTerm c@Const {} = return (False, c)
optimizeTerm (Lam i x ty t) = 
  do (b, t') <- optimizeTerm (open x t)
     return (b, Lam i x ty (close x t'))
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
     return (b, Fix i x xty f fty (close2 f x t'))
optimizeTerm z@(IfZ i (Const {}) t e) = deadCode z
optimizeTerm (IfZ i c t e) = 
  do (bc, c') <- optimizeTerm c
     (bt, t') <- optimizeTerm t
     (be, e') <- optimizeTerm e
     return (bc || bt || be, IfZ i c' t' e')
optimizeTerm l@(Let i x ty def t) = 
  do (b, l') <- deadCode l
     if b 
     then return (b, l')
     else do def' <- consFold def
             case def' of 
              (True, Const {}) -> constProg (Let i x ty (snd def') t)
              (False, _) -> inlineExp l
              res -> return res

-- Funciones auxiliares

hasPrint :: MonadFD4 m => TTerm -> m Bool
hasPrint (V _ (Global n)) = 
  do d <- lookupDecl n
     case d of
       Just t -> hasPrint t
       _ -> failFD4 "Global variable not assigned"
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

hasVar :: Int -> TTerm -> Bool
hasVar n (V _ (Bound i)) = n == i
hasVar _ (V _ _) = False 
hasVar n (Lam _ _ _ (Sc1 t)) = hasVar (n+1) t
hasVar n (App p l r) = hasVar n l || hasVar n r
hasVar n (Fix p f fty x xty (Sc2 t)) = hasVar (n+2) t
hasVar n (IfZ p c t e) = hasVar n c || hasVar n t || hasVar n e
hasVar _ t@(Const _ _) = False
hasVar n (Print p str t) = hasVar n t
hasVar n (BinaryOp p op t u) = hasVar n t || hasVar n u
hasVar n (Let p v vty m (Sc1 o)) = hasVar n m || hasVar (n+1) o