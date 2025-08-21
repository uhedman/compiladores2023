module Optimize
  ( optimizeDecl, optimizeTerm, deadCodeGlobal )
 where

import Lang
    ( BinaryOp(Sub, Add),
      Const(CNat),
      Decl(DeclTy, Decl),
      Scope(Sc1),
      Scope2(Sc2),
      TTerm,
      Tm(..),
      Var(..),
      Name )
import MonadFD4 ( lookupDecl, MonadFD4, failPosFD4 )
import Subst
import Control.Monad.Extra ( (||^) )
import PPrint (ppName)
import Common ( Pos(NoPos), abort )

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

deadCodeGlobal :: MonadFD4 m => [Decl TTerm] -> m [Decl TTerm]
deadCodeGlobal [] = abort "Lista vacia de declaraciones"
deadCodeGlobal [d] = return [d]
deadCodeGlobal (d@(Decl p x t) : ds) = do
  -- 1. primero limpiar el resto
  ds' <- deadCodeGlobal ds
  -- 2. ahora preguntar si x aparece en ds'
  used <- or <$> mapM (hasGlobalVar' x) ds'
  b <- hasPrint t
  if b || used
    then return (d : ds')
    else return ds'
deadCodeGlobal (d : ds) = do
  ds' <- deadCodeGlobal ds
  return (d : ds')

-- Dead code elimination
deadCodeTerm :: MonadFD4 m => TTerm -> m (Bool, TTerm)
deadCodeTerm l@(Let _ x _ def (Sc1 t)) = 
  do b <- hasPrint def
     if b || hasVar 0 t
     then return (False, l)
     else return (True, open x (Sc1 t))
deadCodeTerm (IfZ _ (Const _ (CNat n)) t e) = 
  if n == 0 then return (True, t)
            else return (True, e)
deadCodeTerm t = return (False, t)

-- Constant Propagation
constProp :: MonadFD4 m => TTerm -> m (Bool, TTerm)
constProp (Let _ _ _ c@(Const _ _) t) = return (True, subst c t)
constProp t = return (False, t)

-- | Inline expansion
inlineExp :: MonadFD4 m => TTerm -> m (Bool, TTerm)
inlineExp l@(Let (p, ty) z zty lam@(Lam _ _ _ (Sc1 def)) (Sc1 body)) = 
  do b <- hasPrint def
     if not b && countVar 0 body == 1
     then let (b', body') = search 0 body
          in if b' 
             then return (True, Let (p, ty) z zty lam (close z body'))
             else return (False, l)
     else return (False, l)
  where 
    search :: Int -> TTerm -> (Bool, TTerm)
    search n v@V {} = (False, v)
    search n c@Const {} = (False, c)
    search n (Lam i v vty (Sc1 t)) =
      let (b', t') = search (n+1) t
      in  (b', Lam i v vty (Sc1 t'))
    search n (App i v@(V _ (Bound m)) t) =
      if m == n 
      then expand t
      else let (b', t') = search n t
           in  (b', App i v t')
    search n (App i s t) =
      let (bs, s') = search n s
          (bt, t') = search n t
      in  (bs || bt, App i s' t')
    search n (Print i s t) =
      let (b', t') = search n t
      in  (b', Print i s t')
    search n (BinaryOp i op s t) =
      let (bs, s') = search n s
          (bt, t') = search n t
      in  (bs || bt, BinaryOp i op s' t')
    search n (Fix i f fty x xty (Sc2 t)) =
      let (b', t') = search (n+2) t
      in  (b', Fix i f fty x xty (Sc2 t'))
    search n (IfZ i c t e) =
      let (bc, c') = search n c
          (bt, t') = search n t
          (be, e') = search n e
      in  (bc || bt || be, IfZ i c' t' e')
    search n (Let i x xty d (Sc1 b)) = 
      let (bd, d') = search n d
          (bb, b') = search (n+1) b
      in  (bd || bb, Let i x xty d' (Sc1 b'))
    expand :: TTerm -> (Bool, TTerm)
    expand v@(V _ (Bound _)) = (False, v)
    expand v@(V {}) = (True, subst v (Sc1 def))
    expand c@Const {} = (True, subst c (Sc1 def))
    expand t = (True, Let (NoPos, ty) z ty t (Sc1 def))
inlineExp l@(Let _ _ _ Fix {} _) = return (False, l)
inlineExp t@(App i (V i' (Global l)) r) = 
  do d <- lookupDecl l
     case d of
       Just l' -> return (True, App i l' r)
       Nothing -> return (False, t)
inlineExp (App _ (Lam _ x ty t) r) = 
  case r of 
    V {} -> return (True, subst r t)
    Const {} -> return (True, subst r t)
    _ -> return (True, Let (NoPos, ty) x ty r t)
inlineExp t = return (False, t)

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
optimizeTerm (App i l r) = 
  do (b, t) <- inlineExp (App i l r)
     if b
     then return (True, t)
     else do (bl, l') <- optimizeTerm l
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
optimizeTerm z@(IfZ i (Const {}) t e) = deadCodeTerm z
optimizeTerm (IfZ i c t e) = 
  do (bc, c') <- optimizeTerm c
     (bt, t') <- optimizeTerm t
     (be, e') <- optimizeTerm e
     return (bc || bt || be, IfZ i c' t' e')
optimizeTerm l@(Let i x ty def t) = do
  (bd, ld) <- deadCodeTerm l
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
            else do 
              (bp, lp) <- constProp l
              if bp
                then return (True, lp)
                else inlineExp l

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

-- | Busca la variable global x en el término t
hasGlobalVar' :: MonadFD4 m => Name -> Decl TTerm -> m Bool
hasGlobalVar' x (Decl _ _ t) = hasGlobalVar x t
hasGlobalVar' _ DeclTy {} = return False

hasGlobalVar :: MonadFD4 m => Name -> TTerm -> m Bool
hasGlobalVar x (V (p, ty) (Global nm)) = 
  if x == nm 
  then return True
  else do d <- lookupDecl nm
          case d of
            Just t -> hasGlobalVar x t
            Nothing -> failPosFD4 p $ "Error de ejecución: variable no declarada: " ++ ppName nm
hasGlobalVar _ (V _ _) = return False 
hasGlobalVar _ Const {} = return False
hasGlobalVar x (Lam _ _ _ (Sc1 t)) = hasGlobalVar x t
hasGlobalVar x (App _ l r) = hasGlobalVar x l ||^ hasGlobalVar x r
hasGlobalVar x (Fix _ _ _ _ _ (Sc2 t)) = hasGlobalVar x t
hasGlobalVar x (IfZ _ c t e) = hasGlobalVar x c ||^ hasGlobalVar x t ||^ hasGlobalVar x e
hasGlobalVar x (Print _ _ t) = hasGlobalVar x t
hasGlobalVar x (BinaryOp _ _ t u) = hasGlobalVar x t ||^ hasGlobalVar x u
hasGlobalVar x (Let _ _ _ def (Sc1 body)) = hasGlobalVar x def ||^ hasGlobalVar x body

-- | Busca la variable Bound n en el término t
hasVar :: Int -> TTerm -> Bool
hasVar n (V _ (Bound i)) = n == i
hasVar _ V {} = False 
hasVar n Const {} = False
hasVar n (Lam _ _ _ (Sc1 t)) = hasVar (n+1) t
hasVar n (App _ l r) = hasVar n l || hasVar n r
hasVar n (Fix _ _ _ _ _ (Sc2 t)) = hasVar (n+2) t
hasVar n (IfZ _ c t e) = hasVar n c || hasVar n t || hasVar n e
hasVar n (Print _ _ t) = hasVar n t
hasVar n (BinaryOp _ _ t u) = hasVar n t || hasVar n u
hasVar n (Let _ _ _ def (Sc1 body)) = hasVar n def || hasVar (n+1) body

-- | Cuenta las repeticiones de la variable Bound n en el término t
countVar :: Int -> TTerm -> Int
countVar n (V _ (Bound i)) = if n == i then 1 else 0
countVar n V {} = 0 
countVar n Const {} = 0
countVar n (Lam _ _ _ (Sc1 t)) = countVar (n+1) t
countVar n (App p l r) = countVar n l + countVar n r
countVar n (Fix p f fty x xty (Sc2 t)) = countVar (n+2) t
countVar n (IfZ p c t e) = countVar n c + countVar n t + countVar n e
countVar n (Print p str t) = countVar n t
countVar n (BinaryOp p op t u) = countVar n t + countVar n u
countVar n (Let p v vty def (Sc1 body)) = countVar n def + countVar (n+1) body