{-# LANGUAGE PatternSynonyms #-}
{-# OPTIONS_GHC -Wno-missing-signatures #-}
{-|
Module      : Bytecompile
Description : Compila a bytecode. Ejecuta bytecode.
Copyright   : (c) Mauro Jaskelioff, Guido Martínez, 2020.
License     : GPL-3
Maintainer  : mauro@fceia.unr.edu.ar
Stability   : experimental

Este módulo permite compilar módulos a la Macchina. También provee
una implementación de la Macchina para ejecutar el bytecode.
-}
module Bytecompile
  (Bytecode, runBC, bcWrite, bcRead, bytecompileModule, showBC)
 where

import Lang
    ( getTy,
      BinaryOp(Sub, Add),
      Const(CNat),
      Decl(..),
      Module,
      Scope(Sc1),
      Scope2(Sc2),
      TTerm,
      Tm(..),
      Var(..) )
import MonadFD4
    ( failPosFD4,
      printFD4,
      printStrFD4,
      MonadFD4,
      addOp,
      setMem,
      addClos)
import Subst ( close )

import qualified Data.ByteString.Lazy as BS
import Data.Binary ( Word32, Binary(put, get), decode, encode )
import Data.Binary.Put ( putWord32le )
import Data.Binary.Get ( getWord32le, isEmpty )

import Data.List (intercalate)
import Data.Char ( ord, chr )
import Common (abort)

type Opcode = Int
type Bytecode = [Int]

newtype Bytecode32 = BC { un32 :: [Word32] }
data Val = 
    N Int
  | C ([Val], Bytecode)
  | RA ([Val], Bytecode)

{- Esta instancia explica como codificar y decodificar Bytecode de 32 bits -}
instance Binary Bytecode32 where
  put (BC bs) = mapM_ putWord32le bs
  get = go
    where go =
           do
            empty <- isEmpty
            if empty
              then return $ BC []
              else do x <- getWord32le
                      BC xs <- go
                      return $ BC (x:xs)

{- Estos sinónimos de patrón nos permiten escribir y hacer
pattern-matching sobre el nombre de la operación en lugar del código
entero, por ejemplo:

   f (CALL : cs) = ...

 Notar que si hubieramos escrito algo como
   call = 5
 no podríamos hacer pattern-matching con `call`.

 En lo posible, usar estos códigos exactos para poder ejectutar un
 mismo bytecode compilado en distintas implementaciones de la máquina.
-}
pattern NULL     = 0
pattern RETURN   = 1
pattern CONST    = 2
pattern ACCESS   = 3
pattern FUNCTION = 4
pattern CALL     = 5
pattern ADD      = 6
pattern SUB      = 7
pattern CJUMP    = 8
pattern FIX      = 9
pattern STOP     = 10
pattern SHIFT    = 11
pattern DROP     = 12
pattern PRINT    = 13
pattern PRINTN   = 14
pattern JUMP     = 15
pattern TAILCALL = 16

--función util para debugging: muestra el Bytecode de forma más legible.
showOps :: Bytecode -> [String]
showOps [] = []
showOps (NULL:xs)        = "NULL" : showOps xs
showOps (RETURN:xs)      = "RETURN" : showOps xs
showOps (CONST:i:xs)     = ("CONST " ++  show i) : showOps xs
showOps (ACCESS:i:xs)    = ("ACCESS " ++ show i) : showOps xs
showOps (FUNCTION:i:xs)  = ("FUNCTION len=" ++ show i) : showOps xs
showOps (CALL:xs)        = "CALL" : showOps xs
showOps (TAILCALL:xs)    = "TAILCALL" : showOps xs
showOps (ADD:xs)         = "ADD" : showOps xs
showOps (SUB:xs)         = "SUB" : showOps xs
showOps (CJUMP:i:xs)     = ("CJUMP off=" ++ show i) : showOps xs
showOps (FIX:xs)         = "FIX" : showOps xs
showOps (STOP:xs)        = "STOP" : showOps xs
showOps (JUMP:i:xs)      = ("JUMP off=" ++ show i) : showOps xs
showOps (SHIFT:xs)       = "SHIFT" : showOps xs
showOps (DROP:xs)        = "DROP" : showOps xs
showOps (PRINT:xs)       = let (msg,_:rest) = span (/=NULL) xs
                           in  ("PRINT " ++ show (bc2string msg)) : showOps rest
showOps (PRINTN:xs)      = "PRINTN" : showOps xs
showOps (ADD:xs)         = "ADD" : showOps xs
showOps (x:xs)           = show x : showOps xs

showBC :: Bytecode -> String
showBC = intercalate "; " . showOps

showVal :: Val -> String
showVal (N n) = show n
showVal (C (ef, cf)) = "C (ef, " ++ showBC cf ++ ")"
showVal (RA (ef, cf)) = "RA (ef, " ++ showBC cf ++ ")"

bcd :: MonadFD4 m => [Int] -> TTerm -> m Bytecode
bcd ms (Let _ x _ def (Sc1 body)) =
  do def' <- bcd ms def
     case x of
       "_" -> do body' <- bcd (1:ms) body 
                 return $ def' ++ [SHIFT, DROP] ++ body'
       _   -> do body' <- bcd (0:ms) body
                 return $ def' ++ [SHIFT] ++ body' ++ [DROP]
bcd ms t = bcc ms t

bct :: MonadFD4 m => [Int] -> TTerm -> m Bytecode
bct ms (App _ l r) = 
  do l' <- bcd ms l
     r' <- bcd ms r
     return $ l' ++ r' ++ [TAILCALL]
bct ms (IfZ _ c t e) =
  do c' <- bcd ms c
     t' <- bct ms t
     e' <- bct ms e
     return $ c' ++ [CJUMP, length t'] ++ t' ++ e'
bct ms (Let _ x _ def (Sc1 body)) = 
  do def' <- bcd ms def
     case x of
       "_" -> do body' <- bct (1:ms) body 
                 return $ def' ++ [SHIFT, DROP] ++ body'
       _   -> do body' <- bct (0:ms) body
                 return $ def' ++ [SHIFT] ++ body'
bct ms t = do t' <- bcd ms t
              return $ t' ++ [RETURN]

bcc :: MonadFD4 m => [Int] -> TTerm -> m Bytecode
bcc ms (V _ (Bound n)) = 
  let m = sum (take n ms)
  in return [ACCESS, n-m]
bcc _ (V (p, _) (Free nm)) = failPosFD4 p "No deberian haber variables libres"
bcc _ (V (p, _) (Global nm)) = failPosFD4 p "No deberian haber variables libres"
bcc _ (Const _ (CNat n)) = return [CONST, n]
bcc ms (Lam _ _ _ (Sc1 s)) = 
  do s' <- bct ms s
     return $ [FUNCTION, length s'] ++ s'
bcc ms (App _ l r) = 
  do l' <- bcd ms l
     r' <- bcd ms r
     return $ l' ++ r' ++ [CALL]
bcc ms (Print _ str t) = 
  do t' <- bcd ms t
     return $ t' ++ [PRINT] ++ string2bc str ++ [NULL, PRINTN]
bcc ms (BinaryOp _ Add l r) = 
  do l' <- bcd ms l
     r' <- bcd ms r
     return $ l' ++ r' ++ [ADD]
bcc ms (BinaryOp _ Sub l r) = 
  do l' <- bcd ms l
     r' <- bcd ms r
     return $ l'++r'++[SUB]
bcc ms (Fix _ _ _ _ _ (Sc2 s)) = 
  do s' <- bct ms s
     return $ [FUNCTION, length s'] ++ s' ++ [FIX]
bcc ms (IfZ _ c t e) =
  do c' <- bcd ms c
     t' <- bcd ms t
     e' <- bcd ms e
     return $ c' ++ [CJUMP, length t' + 2] ++ t' ++ [JUMP, length e'] ++ e'
bcc ms (Let _ x _ def (Sc1 body)) = 
  do def' <- bcd ms def
     case x of
       "_" -> do body' <- bcc (1:ms) body 
                 return $ def' ++ [SHIFT, DROP] ++ body'
       _   -> do body' <- bcc (0:ms) body
                 return $ def' ++ [SHIFT] ++ body'

-- ord/chr devuelven los codepoints unicode, o en otras palabras
-- la codificación UTF-32 del caracter.
string2bc :: String -> Bytecode
string2bc = map ord

bc2string :: Bytecode -> String
bc2string = map chr

glob2free :: TTerm -> TTerm
glob2free (V p (Global n)) = V p (Free n)
glob2free c@(Const _ _) = c
glob2free (Lam i x xty (Sc1 t)) = Lam i x xty (Sc1 (glob2free t))
glob2free (App i l r) = App i (glob2free l) (glob2free r)
glob2free (Print i s t) = Print i s (glob2free t)
glob2free (BinaryOp i op l r) = BinaryOp i op (glob2free l) (glob2free r)
glob2free (Fix i f fty x xty (Sc2 t)) = Fix i f fty x xty (Sc2 (glob2free t))
glob2free (IfZ i c t e) = IfZ i (glob2free c) (glob2free t) (glob2free e)
glob2free (Let i x xty def (Sc1 t)) = Let i x xty (glob2free def) (Sc1 (glob2free t))
glob2free t = t

-- | Transforma un modulo con variables globales a
-- un solo termino con variables libres, conectando
-- las declaraciones con Let.
translate :: [Decl TTerm] -> TTerm
translate [] = abort "Lista de declaraciones vacia"
translate [Decl p _ _ b] = glob2free b
translate (Decl p n _ b:ds) = Let (p, getTy b) n (getTy b) (glob2free b) (close n (translate ds))
translate (DeclTy _ _ b:ds) = translate ds

bytecompileModule :: MonadFD4 m => Module -> m Bytecode
bytecompileModule m = 
  do bc <- (bcc [] . translate) m
     -- abort $ showBC bc
     return $ bc ++ [STOP]

-- | Toma un bytecode, lo codifica y lo escribe un archivo
bcWrite :: Bytecode -> FilePath -> IO ()
bcWrite bs filename = BS.writeFile filename (encode $ BC $ fromIntegral <$> bs)

---------------------------
-- * Ejecución de bytecode
---------------------------

-- | Lee de un archivo y lo decodifica a bytecode
bcRead :: FilePath -> IO Bytecode
bcRead filename = (map fromIntegral <$> un32) . decode <$> BS.readFile filename

runBC :: MonadFD4 m => Bytecode -> m ()
runBC bc = go (bc, [], [])
  where go :: MonadFD4 m => (Bytecode, [Val], [Val]) -> m ()
        go (CONST:n:c, e, s) = addOp >> setMem (length s + 1) >> go (c, e, N n:s)
        go (ADD:c, e, N m:N n:s) = addOp >> go (c, e, N (m+n):s)
        go (SUB:c, e, N m:N n:s) = addOp >> go (c, e, N (max (n-m) 0):s)
        go (ACCESS:i:c, e, s) = addOp >> setMem (length s + 1) >> go (c, e, e!!i:s)
        go (CALL:c, e, v:C (ef,cf):s) = addOp >> go (cf, v:ef, RA (e,c):s)
        go (TAILCALL:c, e, v:C (ef,cf):s) = addOp >> go (cf, v:ef, s)
        go (FUNCTION:n:c, e, s) = 
          let (f,c') = splitAt n c
          in  addOp >> addClos >> setMem (length s + 1) >> go (c', e, C (e, f):s)
        go (RETURN:_, _, v:RA (e,c):s) = addOp >> go (c, e, v:s)
        go (FIX:c, e, C (ef,cf):s) = 
          let efix = C (efix, cf):ef
          in  addOp >> addClos >> go (c, e, C (efix, cf):s)
        go (SHIFT:c, e, v:s) = addOp >> go (c, v:e, s)
        go (DROP:c, _:e, s) = addOp >> go (c, e, s)
        go (PRINTN:c, e, N n:s) = 
          do printFD4 (show n)
             addOp >> go (c, e, N n:s)
        go (PRINT:c, e, s) = 
          do let (str,_:c') = span (/=NULL) c
             printStrFD4 $ bc2string str
             addOp >> go (c', e, s)
        go (CJUMP:l:c, e, N n:s) = 
          if n == 0
          then addOp >> go (c, e, s)
          else addOp >> go (drop l c, e, s)
        go (JUMP:n:c, e, s) = addOp >> go (drop n c, e, s)
        go (STOP:_, _, _) = addOp
        go (c, e, s) = abort $ "Patron no reconocido: <" ++ showBC c ++ ",\n" ++ concatMap showVal e ++ ",\n" ++ concatMap showVal s ++ ">"
