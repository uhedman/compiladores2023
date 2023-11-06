{-|
Module      : Global
Description : Define el estado global del compilador
Copyright   : (c) Mauro Jaskelioff, Guido Martínez, 2020.
License     : GPL-3
Maintainer  : mauro@fceia.unr.edu.ar
Stability   : experimental

-}
module Global where

import Lang

data GlEnv = GlEnv {
  inter :: Bool,        --  ^ True, si estamos en modo interactivo.
                        -- Este parámetro puede cambiar durante la ejecución:
                        -- Es falso mientras se cargan archivos, pero luego puede ser verdadero.
  lfile :: String,      -- ^ Último archivo cargado.
  cantDecl :: Int,      -- ^ Cantidad de declaraciones desde la última carga
  glb :: [Decl TTerm],  -- ^ Entorno con declaraciones globales
  env :: [(Name, Ty)]   -- ^ Entorno con declaraciones de tipos globales
}

-- ^ Entorno de tipado de declaraciones globales
tyEnv :: GlEnv ->  [(Name,Ty)]
tyEnv g = map f (glb g) ++ env g
  where f (Decl _ n b) = (n, getTy b)
        f (DeclTy _ n ty) = (n, ty)

{-
 Tipo para representar las banderas disponibles en línea de comando.
-}
data Mode =
    Interactive
  | Typecheck
  | Eval
  | Bytecompile
  | RunVM
  | CC
  -- | Canon
  -- | Assembler
  -- | Build
data Conf = Conf {
    opt :: Bool,          --  ^ True, si estan habilitadas las optimizaciones.
    cek :: Bool,          --  ^ True, si se utiliza la CEK.
    modo :: Mode
}

-- | Valor del estado inicial
initialEnv :: GlEnv
initialEnv = GlEnv False "" 0 [] []
