{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use record patterns" #-}
{-|
Module      : PPrint
Description : Pretty printer para FD4.
Copyright   : (c) Mauro Jaskelioff, Guido Martínez, 2020.
License     : GPL-3
Maintainer  : mauro@fceia.unr.edu.ar
Stability   : experimental

-}

module PPrint (
    pp,
    ppTy,
    ppName,
    ppDecl
    ) where

import Lang
import Subst ( open, open2 )
import Common ( Pos )

import Data.Text ( unpack )
import Prettyprinter.Render.Terminal
  ( renderStrict, italicized, color, colorDull, Color (..), AnsiStyle )
import Prettyprinter
    ( (<+>),
      annotate,
      defaultLayoutOptions,
      layoutSmart,
      nest,
      sep,
      parens,
      Doc,
      Pretty(pretty) )
import MonadFD4 ( gets, MonadFD4 )
import Global ( GlEnv(glb) )

freshen :: [Name] -> Name -> Name
freshen ns n = let cands = n : map (\i -> n ++ show i) [0..] 
               in head (filter (`notElem` ns) cands)

-- | 'openAll' convierte términos locally nameless
-- a términos fully named abriendo todos las variables de ligadura que va encontrando
-- Debe tener cuidado de no abrir términos con nombres que ya fueron abiertos.
-- Estos nombres se encuentran en la lista ns (primer argumento).
openAll :: (i -> Pos) -> [Name] -> Tm i Var -> STerm
openAll gp ns (V p v) = case v of 
      Bound i ->  SV (gp p) $ "(Bound "++show i++")" --este caso no debería aparecer
                                               --si el término es localmente cerrado
      Free x -> SV (gp p) x
      Global x -> SV (gp p) x
openAll gp ns (Const p c) = SConst (gp p) c
openAll gp ns (Lam p x ty t) = 
  let x' = freshen ns x 
  in case openAll gp (x':ns) (open x' t) of
        SLam y tys t' -> SLam (gp p) ((x',ty2sty ty):tys) t'
        t' -> SLam (gp p) [(x',ty2sty ty)] t'
openAll gp ns (App p t u) = SApp (gp p) (openAll gp ns t) (openAll gp ns u)
openAll gp ns (Fix p f fty x xty t) = 
  let x' = freshen ns x
      f' = freshen (x':ns) f
  in case openAll gp (x:f:ns) (open2 f' x' t) of
    SLam y tys t' -> SFix (gp p) (f',ty2sty fty) (x',ty2sty xty) tys t'
    t' -> SFix (gp p) (f',ty2sty fty) (x',ty2sty xty) [] t'
openAll gp ns (IfZ p c t e) = SIfZ (gp p) (openAll gp ns c) (openAll gp ns t) (openAll gp ns e)
openAll gp ns (Print p str t) = SPrint (gp p) str (openAll gp ns t)
openAll gp ns (BinaryOp p op t u) = SBinaryOp (gp p) op (openAll gp ns t) (openAll gp ns u)
openAll gp ns (Let p v ty m n) = 
    let v'= freshen ns v 
    in  SLetVar (gp p) (v',ty2sty ty) (openAll gp ns m) (openAll gp (v':ns) (open v' n))

ty2sty :: Ty -> STy
ty2sty NatTy = SNatTy
ty2sty (FunTy t t') = SFun (ty2sty t) (ty2sty t')

--Colores
constColor :: Doc AnsiStyle -> Doc AnsiStyle
constColor = annotate (color Red)
opColor :: Doc AnsiStyle -> Doc AnsiStyle
opColor = annotate (colorDull Green)
keywordColor :: Doc AnsiStyle -> Doc AnsiStyle
keywordColor = annotate (colorDull Green) -- <> bold)
typeColor :: Doc AnsiStyle -> Doc AnsiStyle
typeColor = annotate (color Blue <> italicized)
typeOpColor :: Doc AnsiStyle -> Doc AnsiStyle
typeOpColor = annotate (colorDull Blue)
defColor :: Doc AnsiStyle -> Doc AnsiStyle
defColor = annotate (colorDull Magenta <> italicized)
nameColor :: Doc AnsiStyle -> Doc AnsiStyle
nameColor = id

-- | Pretty printer de nombres (Doc)
names2doc :: [Name] -> Doc AnsiStyle
names2doc ns = sep $ map (nameColor . pretty) ns

-- |  Pretty printer de nombres (String)
ppName :: Name -> String
ppName = id

-- | Pretty printer para tipos (Doc)
sty2doc :: STy -> Doc AnsiStyle
sty2doc SNatTy = typeColor (pretty "Nat")
sty2doc (Syn var) = nameColor (pretty var)
sty2doc (SFun x@(SFun _ _) y) = sep [parens (sty2doc x), typeOpColor (pretty "->"),sty2doc y]
sty2doc (SFun x y) = sep [sty2doc x, typeOpColor (pretty "->"),sty2doc y] 

ty2doc :: Ty -> Doc AnsiStyle
ty2doc NatTy = typeColor (pretty "Nat")
ty2doc (FunTy x@(FunTy _ _) y) = sep [parens (ty2doc x), typeOpColor (pretty "->"),ty2doc y]
ty2doc (FunTy x y) = sep [ty2doc x, typeOpColor (pretty "->"),ty2doc y] 

-- | Pretty printer para tipos (String)
ppTy :: Ty -> String
ppTy = render . ty2doc

c2doc :: Const -> Doc AnsiStyle
c2doc (CNat n) = constColor (pretty (show n))

binary2doc :: BinaryOp -> Doc AnsiStyle
binary2doc Add = opColor (pretty "+")
binary2doc Sub = opColor (pretty "-")

collectApp :: STerm -> (STerm, [STerm])
collectApp = go [] where
  go ts (SApp _ h tt) = go (tt:ts) h
  go ts h = (h, ts)

parenIf :: Bool -> Doc a -> Doc a
parenIf True = parens
parenIf _ = id

-- t2doc at t :: Doc
-- at: debe ser un átomo
-- | Pretty printing de términos (Doc)
t2doc :: Bool     -- Debe ser un átomo? 
      -> STerm    -- término a mostrar
      -> Doc AnsiStyle
-- Uncomment to use the Show instance for STerm
{- t2doc at x = text (show x) -}
t2doc at (SV _ x) = names2doc [x]
t2doc at (SConst _ c) = c2doc c
t2doc at (SLam _ [] t) = t2doc at t
t2doc at (SLam p binds t) =
  parenIf at $
  sep [sep [ keywordColor (pretty "fun")
           , bindings2doc binds
           , opColor(pretty "->")]
      , nest 2 (t2doc False t)]

t2doc at t@(SApp _ _ _) =
  let (h, ts) = collectApp t in
  parenIf at $
  t2doc True h <+> sep (map (t2doc True) ts)

t2doc at (SFix _ (f,fty) (x,xty) binds m) = -- Wip
  parenIf at $
  sep [ sep [keywordColor (pretty "fix")
                  , bindings2doc ((f, fty):(x,xty):binds)
                  , opColor (pretty "->") ]
      , nest 2 (t2doc False m)
      ]

t2doc at (SIfZ _ c t e) =
  parenIf at $
  sep [keywordColor (pretty "ifz"), nest 2 (t2doc False c)
     , keywordColor (pretty "then"), nest 2 (t2doc False t)
     , keywordColor (pretty "else"), nest 2 (t2doc False e) ]

t2doc at (SPrint _ str t) =
  parenIf at $
  sep [keywordColor (pretty "print"), pretty (show str), t2doc True t]

t2doc at (SLetLam _ recBool binds (v,ty) t t') = -- Wip
  parenIf at $
  sep [
    sep [keywordColor (pretty "let")
       , names2doc [v]
       , bindings2doc binds
       , sty2doc ty
       , opColor (pretty "=") ]
  , nest 2 (t2doc False t)
  , keywordColor (pretty "in")
  , nest 2 (t2doc False t') ]

t2doc at (SLetVar _ (v,ty) t t') =
  parenIf at $
  sep [
    sep [keywordColor (pretty "let")
       , bindings2doc [(v,ty)]
       , opColor (pretty "=") ]
  , nest 2 (t2doc False t)
  , keywordColor (pretty "in")
  , nest 2 (t2doc False t') ]

t2doc at (SBinaryOp _ o a b) =
  parenIf at $
  t2doc True a <+> binary2doc o <+> t2doc True b

joinBinds :: [(Name, STy)] -> [([Name], STy)]
joinBinds = foldr f [] 
  where f (n, nty) [] = [([n], nty)]
        f (n, nty) ((ms, mty):xs) = if nty == mty then (n:ms, mty):xs
                                                  else ([n],nty):(ms, mty):xs

bindings2doc :: [(Name, STy)] -> Doc AnsiStyle
bindings2doc binds = sep prettyBinds
  where joinedBinds = joinBinds binds
        prettyBinds = map (\(ns, nty) -> parens (sep [names2doc ns, pretty ":", sty2doc nty])) joinedBinds
-- | Pretty printing de términos (String)
pp :: MonadFD4 m => TTerm -> m String
-- Uncomment to use the Show instance for Term
{- pp = show -}
pp t = do
       gdecl <- gets glb
       return (render . t2doc False $ openAll fst (map declName gdecl) t)

render :: Doc AnsiStyle -> String
render = unpack . renderStrict . layoutSmart defaultLayoutOptions

-- | Pretty printing de declaraciones
ppDecl :: MonadFD4 m => Decl TTerm -> m String
ppDecl (Decl p x t) = do 
  gdecl <- gets glb
  return (render $ sep [defColor (pretty "let")
                       , names2doc [x] 
                       , defColor (pretty "=")] 
                   <+> nest 2 (t2doc False (openAll fst (map declName gdecl) t)))
ppDecl (DeclTy p x t) = do 
  gdecl <- gets glb
  return (render $ sep [defColor (pretty "type")
                       , names2doc [x] 
                       , defColor (pretty "=")
                       , ty2doc t])
