{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RecordWildCards #-}
{-# OPTIONS_GHC -Wno-missing-signatures #-}
{-|
Module      : Bytecompile8
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
import MonadFD4
import Subst ( close )

import qualified Data.ByteString.Lazy as BS
import Data.Binary ( Word8, Binary(put, get), decode, encode )
import Data.Binary.Put ( putWord8 )
import Data.Binary.Get ( getWord8, isEmpty )

import Data.List (intercalate)
import Data.Char
import Data.Bits (Bits(shiftL, shiftR, (.&.)))

type Opcode = Word8
type Bytecode = [Word8]

newtype Bytecode8 = BC { un8 :: [Word8] }
data Val = 
    N Int
  | C ([Val], Bytecode)
  | RA ([Val], Bytecode)

{- Esta instancia explica como codificar y decodificar Bytecode de 8 bits -}
instance Binary Bytecode8 where
  put (BC bs) = mapM_ putWord8 bs
  get = go
    where go =
           do
            empty <- isEmpty
            if empty
              then return $ BC []
              else do x <- getWord8
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
pattern IFZ      = 8
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
showOps (CONST:xs)       = let i = word2int (take 4 xs)
                           in ("CONST " ++ show i) : showOps (drop 4 xs)
showOps (ACCESS:xs)      = let i = word2int (take 4 xs)
                           in ("ACCESS " ++ show i) : showOps (drop 4 xs)
showOps (FUNCTION:xs)    = let i = word2int (take 4 xs)
                           in ("FUNCTION len=" ++ show i) : showOps (drop 4 xs)
showOps (CALL:xs)        = "CALL" : showOps xs
showOps (TAILCALL:xs)    = "TAILCALL" : showOps xs
showOps (ADD:xs)         = "ADD" : showOps xs
showOps (SUB:xs)         = "SUB" : showOps xs
showOps (IFZ:xs)         = let i = word2int (take 4 xs)
                           in ("IFZ JUMP off=" ++ show i) : showOps (drop 4 xs)
showOps (FIX:xs)         = "FIX" : showOps xs
showOps (STOP:xs)        = "STOP" : showOps xs
showOps (JUMP:xs)        = let i = word2int (take 4 xs)
                           in ("JUMP off=" ++ show i) : showOps (drop 4 xs)
showOps (SHIFT:xs)       = "SHIFT" : showOps xs
showOps (DROP:xs)        = "DROP" : showOps xs
showOps (PRINT:xs)       = let (msg,_:rest) = span (/=NULL) xs
                           in ("PRINT " ++ show (bc2string msg)) : showOps rest
showOps (PRINTN:xs)      = "PRINTN" : showOps xs
showOps (ADD:xs)         = "ADD" : showOps xs
showOps (x:xs)           = show x : showOps xs

showBC :: Bytecode -> String
showBC = intercalate "; " . showOps

bct :: MonadFD4 m => TTerm -> m Bytecode
bct (App _ l r) = 
  do l' <- bcc l
     r' <- bcc r
     return $ l'++r'++[TAILCALL]
bct t = bcc t

bcc :: MonadFD4 m => TTerm -> m Bytecode
bcc (V _ (Bound n)) = return $ ACCESS : int2word n
bcc (V _ (Free nm)) = failFD4 "Las variables libres deberian transformarse a indices de de Bruijn"
bcc (V _ (Global nm)) = failFD4 "Las variables globales deberian transformarse a indices de de Bruijn"
bcc (Const _ (CNat n)) = return $ CONST : int2word n
bcc (Lam _ _ _ (Sc1 s)) = 
  do s' <- bct s
     return $ [FUNCTION]++int2word (length s' + 1)++s'++[RETURN]
bcc (App _ l r) = 
  do l' <- bcc l
     r' <- bcc r
     return $ l'++r'++[CALL]
bcc (Print _ str t) = 
  do t' <- bcc t
     return $ t'++[PRINT]++string2bc str++[NULL]++[PRINTN]
bcc (BinaryOp _ Add l r) = 
  do l' <- bcc l
     r' <- bcc r
     return $ l'++r'++[ADD]
bcc (BinaryOp _ Sub l r) = 
  do l' <- bcc l
     r' <- bcc r
     return $ l'++r'++[SUB]
bcc (Fix _ _ _ _ _ (Sc2 s)) = 
  do s' <- bcc s
     return $ [FUNCTION]++int2word (length s' + 1)++s'++[RETURN, FIX]
bcc (IfZ _ c t e) =
  do c' <- bcc c
     t' <- bcc t
     e' <- bcc e
     return $ c' ++ [IFZ]++int2word (length t' + 5)++t'++[JUMP]++int2word (length e')++e'
bcc (Let _ _ _ e1 (Sc1 e2)) = 
  do e1' <- bcc e1
     e2' <- bcc e2
     return $ e1'++[SHIFT]++e2'++[DROP]

-- ord/chr devuelven los codepoints unicode, o en otras palabras
-- la codificación UTF-8 del caracter.
string2bc :: String -> Bytecode
string2bc = map (fromIntegral . ord)

bc2string :: Bytecode -> String
bc2string = map (chr . fromIntegral)

int2word :: Int -> Bytecode
int2word n = let a = fromIntegral $ shiftR n 24
                 b = fromIntegral $ shiftR n 16 .&. 0xFF
                 c = fromIntegral $ shiftR n 8 .&. 0xFF
                 d = fromIntegral $ n .&. 0xFF
             in [a,b,c,d]

word2int :: Bytecode -> Int
word2int [a,b,c,d] = let a' = shiftL (fromIntegral a) 24
                         b' = shiftL (fromIntegral b) 16
                         c' = shiftL (fromIntegral c) 8
                         d' = fromIntegral d
                     in a'+b'+c'+d'
word2int _ = error "Entero sin tamaño 32"

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

translate :: [Decl TTerm] -> TTerm
translate [] = error "Lista de declaraciones vacia"
translate [Decl p _ b] = glob2free b
translate (Decl p n b:ds) = Let (p, getTy b) n (getTy b) (glob2free b) (close n (translate ds))
translate (DeclTy _ _ b:ds) = translate ds

drops2stop :: Bytecode -> Bytecode
drops2stop [] = [STOP]
drops2stop (DROP:c) = if null $ dropWhile (==DROP) c
                      then [STOP]
                      else let (l, r) = span (/=DROP) c
                           in [DROP] ++ l ++ drops2stop r
drops2stop c = let (a,b) = span (/=DROP) c
               in a ++ drops2stop b

bytecompileModule :: MonadFD4 m => Module -> m Bytecode
bytecompileModule m = do bc <- (bcc . translate) m
                         return $ drops2stop bc

-- | Toma un bytecode, lo codifica y lo escribe un archivo
bcWrite :: Bytecode -> FilePath -> IO ()
bcWrite bs filename = BS.writeFile filename (encode $ BC $ fromIntegral <$> bs)

---------------------------
-- * Ejecución de bytecode
---------------------------

-- | Lee de un archivo y lo decodifica a bytecode
bcRead :: FilePath -> IO Bytecode
bcRead filename = (map fromIntegral <$> un8) . decode <$> BS.readFile filename

runBC :: MonadFD4 m => Bytecode -> m ()
runBC bc = go (bc, [], [])
  where go :: MonadFD4 m => (Bytecode, [Val], [Val]) -> m ()
        go (CONST:c, e, s) = let n = word2int $ take 4 c
                             in go (drop 4 c, e, N n:s)
        go (ADD:c, e, N m:N n:s) = go (c, e, N (m+n):s)
        go (SUB:c, e, N m:N n:s) = go (c, e, N (max (n-m) 0):s)
        go (ACCESS:c, e, s) = let i = word2int $ take 4 c
                              in go (drop 4 c, e, e!!i:s)
        go (CALL:c, e, v:C (ef,cf):s) = go (cf, v:ef, RA (e,c):s)
        go (TAILCALL:c, e, v:C (ef,cf):s) = go (cf, v:ef, s)
        go (FUNCTION:c, e, s) = let n = word2int $ take 4 c
                                    (f,c') = splitAt n (drop 4 c)
                                in go (c', e, C (e, f):s)
        go (RETURN:_, _, v:RA (e,c):s) = go (c, e, v:s)
        go (FIX:c, e, C (ef,cf):s) = let efix = C (efix, cf):ef
                                     in go (c, e, C (efix, cf):s)
        go (SHIFT:c, e, v:s) = go (c, v:e, s)
        go (DROP:c, _:e, s) = go (c, e, s)
        go (PRINTN:c, e, N n:s) = do printFD4 (show n)
                                     go (c, e, N n:s)
        go (PRINT:c, e, s) = do let (str,_:c') = span (/=NULL) c
                                printStrFD4 $ bc2string str
                                go (c', e, s)
        go (IFZ:c, e, N n:s) = if n == 0
                               then go (drop 4 c, e, s)
                               else let l = word2int $ take 4 c
                                    in go (drop (l+4) c, e, s)
        go (JUMP:c, e, s) = let n = word2int $ take 4 c
                            in go (drop (n+4) c, e, s)
        go (STOP:_, _, _) = return ()
        go (c, _, _) = error $ "Patron no reconocido: " ++ showBC c
