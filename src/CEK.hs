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
import MonadFD4 (MonadFD4)

data Val = 
    Var Name
  | Fun Name Val
  | Fix Name Name Val

Type Env = [(Name, Val)]

data Frame = 
    FrAppL Frame TTerm
  | FrAppR Val Frame
  | FrIfz Frame TTerm TTerm
  | FrBOpL Frame TTerm
  | FrBOpR Val Frame
  | FrPrint String Frame

Type Kont = [Frame]

seek :: MonadFD4 m => TTerm -> Env -> Kont -> m Val

destroy :: MonadFD4 m => Val -> Kont -> m Val
