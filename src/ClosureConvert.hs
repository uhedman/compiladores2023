module ClosureConvert where

import IR
import Lang
import Control.Monad.Writer
import Control.Monad.State

closureConvert :: Term -> StateT Int (Writer [IrDecl]) Ir
closureConvert = undefined