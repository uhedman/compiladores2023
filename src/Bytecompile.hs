{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RecordWildCards #-}
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
import MonadFD4

import qualified Data.ByteString.Lazy as BS
import Data.Binary ( Word32, Binary(put, get), decode, encode )
import Data.Binary.Put ( putWord32le )
import Data.Binary.Get ( getWord32le, isEmpty )

import Data.List (intercalate)
import Data.Char

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
pattern FIX      = 9
pattern STOP     = 10
pattern SHIFT    = 11
pattern DROP     = 12
pattern PRINT    = 13
pattern PRINTN   = 14
pattern JUMP     = 15

--función util para debugging: muestra el Bytecode de forma más legible.
showOps :: Bytecode -> [String]
showOps [] = []
showOps (NULL:xs)        = "NULL" : showOps xs
showOps (RETURN:xs)      = "RETURN" : showOps xs
showOps (CONST:i:xs)     = ("CONST " ++  show i) : showOps xs
showOps (ACCESS:i:xs)    = ("ACCESS " ++ show i) : showOps xs
showOps (FUNCTION:i:xs)  = ("FUNCTION len=" ++ show i) : showOps xs
showOps (CALL:xs)        = "CALL" : showOps xs
showOps (ADD:xs)         = "ADD" : showOps xs
showOps (SUB:xs)         = "SUB" : showOps xs
showOps (FIX:xs)         = "FIX" : showOps xs
showOps (STOP:xs)        = "STOP" : showOps xs
showOps (JUMP:i:xs)      = ("JUMP off=" ++ show i) : showOps xs
showOps (SHIFT:xs)       = "SHIFT" : showOps xs
showOps (DROP:xs)        = "DROP" : showOps xs
showOps (PRINT:xs)       = let (msg,_:rest) = span (/=NULL) xs
                           in ("PRINT " ++ show (bc2string msg)) : showOps rest
showOps (PRINTN:xs)      = "PRINTN" : showOps xs
showOps (ADD:xs)         = "ADD" : showOps xs
showOps (x:xs)           = show x : showOps xs

showBC :: Bytecode -> String
showBC = intercalate "; " . showOps

bcc :: MonadFD4 m => TTerm -> m Bytecode
bcc (V i (Bound n)) = return [ACCESS,n]
bcc (V i (Free nm)) = failFD4 "Las variables libres deberian transformarse a indices de de Bruijn"
bcc (V i (Global nm)) = failFD4 "Las variables globales deberian transformarse a indices de de Bruijn"
bcc (Const i (CNat n)) = return [CONST,n]
bcc (Lam i n t (Sc1 s)) = 
  do s' <- bcc s
     return $ [FUNCTION, length s']++s'++[RETURN]
bcc (App i l r) = 
  do l' <- bcc l
     r' <- bcc r
     return $ l'++r'++[CALL]
bcc (Print i str t) = 
  do t' <- bcc t
     return $ t'++[PRINT]++string2bc str++[NULL]
bcc (BinaryOp i Add l r) = 
  do l' <- bcc l
     r' <- bcc r
     return $ l'++r'++[ADD]
bcc (BinaryOp i Sub l r) = 
  do l' <- bcc l
     r' <- bcc r
     return $ l'++r'++[SUB]
bcc (Fix i f fty x xty (Sc2 s)) = 
  do s' <- bcc s
     return $ [FUNCTION, length s'] ++ s' ++ [RETURN, FIX]
bcc (IfZ i c t e) = -- usar JUMP?
  do c' <- bcc c
     t' <- bcc c
     e' <- bcc c
     case c' of
       [0] -> return t'
       [n] -> return e'
       res -> failFD4 "Resultado inesperado" 
bcc (Let i x xty e1 (Sc1 e2)) = 
  do e1' <- bcc e1
     e2' <- bcc e2
     return $ e1'++[SHIFT]++e2'++[DROP]

-- ord/chr devuelven los codepoints unicode, o en otras palabras
-- la codificación UTF-32 del caracter.
string2bc :: String -> Bytecode
string2bc = map ord

bc2string :: Bytecode -> String
bc2string = map chr

translate :: [Decl TTerm] -> TTerm
translate [] = error "Lista de declaraciones vacia"
translate [Decl p n b] = b
translate (Decl p n b:ds) = Let (p, getTy b) n (getTy b) b (Sc1 (translate ds))
translate _ = error "No se esperaba una declaracion de tipo"

bytecompileModule :: MonadFD4 m => Module -> m Bytecode
bytecompileModule m = do bc <- (bcc . translate) m
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

nth :: (Eq t, Num t) => t -> [a] -> a
nth 0 (x:_) = x
nth n (_:xs) = nth (n-1) xs
nth _ _ = error "Indice fuera de rango"

runBC :: MonadFD4 m => Bytecode -> m ()
runBC bc = go (bc, [], [])
  where go :: MonadFD4 m => (Bytecode, [Val], [Val]) -> m ()
        go (CONST:n:c, e, s) = go (c, e, N n:s)
        go (ADD:c, e, N m:N n:s) = go (c, e, N (m+n):s)
        go (SUB:c, e, N m:N n:s) = go (c, e, N (m-n):s)
        go (ACCESS:i:c, e, m:n:s) = go (c, e, nth i e:s)
        go (CALL:c, e, v:C (ef,cf):s) = go (cf, v:ef, RA (e,c):s)
        go (FUNCTION:n:c, e, s) = go (drop n c, e, C (e, take n c):s)
        go (RETURN:_, _, v:RA (e,c):s) = go (c, e, v:s)
        go (FIX:c, e, C (ef,cf):s) = let efix = C (efix, cf):ef
                                     in go (c, e, C (efix, cf):s)
        go (SHIFT:c, e, v:s) = go (c, v:e, s)
        go (DROP:c, _:e, s) = go (c, e, s)
        -- go (PRINTN:c, e, N n:s) = do printFD4 (show n)
        --                              go (c, e, N n:s)
        go (PRINT:c, e, N n:s) = do let str = takeWhile (/= NULL) c
                                    let c' = tail $ dropWhile (/= NULL) c
                                    printFD4 $ bc2string str ++ show n
                                    go (c', e, s)
        go (JUMP:n:c, e, s) = go (drop n c, e, s)
        go (STOP:_, _, _) = return ()
        go (c, _, _) = error $ "Patron no reconocido" ++ show c
