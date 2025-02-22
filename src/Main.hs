{-# LANGUAGE RecordWildCards #-}

{-|
Module      : Main
Description : Compilador de FD4.
Copyright   : (c) Mauro Jaskelioff, Guido Martínez, 2020.
License     : GPL-3
Maintainer  : mauro@fceia.unr.edu.ar
Stability   : experimental

-}

module Main where

import System.Console.Haskeline ( defaultSettings, getInputLine, runInputT, InputT )
import Control.Monad.Catch (MonadMask)

--import Control.Monad
import Control.Monad.Trans
import Data.List (nub, isPrefixOf, intercalate )
import Data.Char ( isSpace )
import Control.Exception ( catch , IOException )
import System.IO ( hPrint, stderr, hPutStrLn )
import Data.Maybe ( fromMaybe )

import System.Exit ( exitWith, ExitCode(ExitFailure) )
import Options.Applicative

import Global
import Errors
import Lang
import Parse ( P, tm, program, declOrTm, runP )
import Elab ( elab, elabDecl )
import Eval ( eval )
import PPrint ( pp , ppTy, ppDecl, ppStats )
import MonadFD4
import TypeChecker ( tc, tcDecl )
import CEK ( evalCEK )
import Bytecompile ( runBC, bytecompileModule, bcWrite, bcRead )
import Optimize ( optimizeDecl )
import System.FilePath ( dropExtension )
import qualified Control.Monad
import C (ir2C)
import IR (IrDecls (IrDecls))
import ClosureConvert (runCC)

prompt :: String
prompt = "FD4> "

-- | Parser de banderas
parseMode :: Parser (Mode,Bool,Bool,Bool)
parseMode = (,,,) <$>
      (flag' Typecheck ( long "typecheck" <> short 't' <> help "Chequear tipos e imprimir el término")
      <|> flag' Bytecompile (long "bytecompile" <> short 'm' <> help "Compilar a la BVM")
      <|> flag' RunVM (long "runVM" <> short 'r' <> help "Ejecutar bytecode en la BVM")
      <|> flag Interactive Interactive (long "interactive" <> short 'i' <> help "Ejecutar en forma interactiva")
      <|> flag Eval        Eval        (long "eval" <> short 'e' <> help "Evaluar programa")
      <|> flag' CC ( long "cc" <> short 'c' <> help "Compilar a código C")
  -- <|> flag' Canon ( long "canon" <> short 'n' <> help "Imprimir canonicalización")
  -- <|> flag' Assembler ( long "assembler" <> short 'a' <> help "Imprimir Assembler resultante")
  -- <|> flag' Build ( long "build" <> short 'b' <> help "Compilar")
      )
   <*> flag False True (long "optimize" <> short 'o' <> help "Optimizar código")
   <*> flag False True (long "cek" <> short 'k' <> help "Utilizar la CEK")
   <*> flag False True (long "profiling" <> short 'p' <> help "Mostrar metricas del programa")

-- | Parser de opciones general, consiste de un modo y una lista de archivos a procesar
parseArgs :: Parser (Mode,Bool,Bool,Bool, [FilePath])
parseArgs = (\(m,o,c,p) f -> (m,o,c,p,f)) <$> parseMode <*> many (argument str (metavar "FILES..."))

main :: IO ()
main = execParser opts >>= go
  where
    opts = info (parseArgs <**> helper)
      ( fullDesc
     <> progDesc "Compilador de FD4"
     <> header "Compilador de FD4 de la materia Compiladores 2022" )

    go :: (Mode,Bool,Bool,Bool,[FilePath]) -> IO ()
    go (Interactive,opt,cek,prof,files) =
      if prof then runOrFail (Conf opt cek prof Interactive) $ Right (runInputT defaultSettings (repl files))
              else runOrFail (Conf opt cek prof Interactive) $ Left (runInputT defaultSettings (repl files))
    go (Bytecompile,opt,cek,prof,files) =
      if prof then runOrFail (Conf opt cek prof RunVM) $ Right $ mapM_ bytecompileFile files
              else runOrFail (Conf opt cek prof RunVM) $ Left $ mapM_ bytecompileFile files
    go (CC,opt,cek,prof,files) =
      if prof then runOrFail (Conf opt cek prof RunVM) $ Right $ mapM_ ccompileFile files
              else runOrFail (Conf opt cek prof RunVM) $ Left $ mapM_ ccompileFile files
    go (RunVM,opt,cek,prof,files) =
      if prof then runOrFail (Conf opt cek prof RunVM) $ Right $ mapM_ runVMFile files
              else runOrFail (Conf opt cek prof RunVM) $ Left $ mapM_ runVMFile files
    go (m,opt,cek,prof,files) =
      if prof then runOrFail (Conf opt cek prof m) $ Right $ mapM_ compileFile files
              else runOrFail (Conf opt cek prof m) $ Left $ mapM_ compileFile files   

runOrFail :: Conf -> Either (FD4 a) (FD4Prof a) -> IO a
runOrFail c m = do
  r <- case m of 
         Left noProf -> runFD4 noProf c
         Right prof -> runFD4Prof prof c
  case r of
    Left err -> do
      liftIO $ hPrint stderr err
      exitWith (ExitFailure 1)
    Right v -> return v

repl :: (MonadFD4 m, MonadMask m) => [FilePath] -> InputT m ()
repl args = do
       lift $ setInter True
       lift $ catchErrors $ mapM_ compileFile args
       s <- lift get
       when (inter s) $ liftIO $ putStrLn
         (  "Entorno interactivo para FD4.\n"
         ++ "Escriba :? para recibir ayuda.")
       loop
  where loop = do
           minput <- getInputLine prompt
           case minput of
               Nothing -> return ()
               Just "" -> loop
               Just x -> do
                       c <- liftIO $ interpretCommand x
                       b <- lift $ catchErrors $ handleCommand c
                       maybe loop (`when` loop) b

loadFile ::  MonadFD4 m => FilePath -> m [SDecl STerm]
loadFile f = do
    let filename = reverse(dropWhile isSpace (reverse f))
    x <- liftIO $ catch (readFile filename)
               (\e -> do let err = show (e :: IOException)
                         hPutStrLn stderr ("No se pudo abrir el archivo " ++ filename ++ ": " ++ err)
                         return "")
    setLastFile filename
    parseIO filename program x

runVMFile ::  MonadFD4 m => FilePath -> m ()
runVMFile f = do bc <- liftIO $ bcRead f
                 runBC bc
                 p <- getProf
                 Control.Monad.when p $ do stats <- getStats
                                           printFD4 (ppStats stats)

bytecompileFile :: MonadFD4 m => FilePath -> m ()
bytecompileFile f = do
  decls <- loadFile f
  tds <- mapM aux decls
  bc <- bytecompileModule tds
  liftIO $ bcWrite bc (dropExtension f ++ ".bc32") -- liftIO?
    where aux d = do td <- typecheckDecl d
                     case td of
                       Decl {} -> do opt <- getOpt
                                     td' <- if opt then optimizeDecl td else return td
                                     addDecl td'
                                     return td'
                       (DeclTy _ x ty) -> do addTy x ty
                                             return td

ccompileFile :: MonadFD4 m => FilePath -> m ()
ccompileFile f = do
  decls <- loadFile f
  tds <- mapM aux decls
  c <- runCC tds
  liftIO $ writeFile (dropExtension f ++ ".c") (ir2C (IrDecls c))-- liftIO?
    where aux d = do td <- typecheckDecl d
                     case td of
                       Decl {} -> do opt <- getOpt
                                     td' <- if opt then optimizeDecl td else return td
                                     addDecl td'
                                     return td'
                       (DeclTy _ x ty) -> do addTy x ty
                                             return td

compileFile ::  MonadFD4 m => FilePath -> m ()
compileFile f = do
    i <- getInter
    setInter False
    when i $ printFD4 ("Abriendo "++f++"...")
    decls <- loadFile f
    mapM_ handleDecl decls
    setInter i

parseIO ::  MonadFD4 m => String -> P a -> String -> m a
parseIO filename p x = case runP p x filename of
                  Left e  -> throwError (ParseErr e)
                  Right r -> return r

evalDecl :: MonadFD4 m => Decl TTerm -> m (Decl TTerm)
evalDecl (Decl p x e) = 
  do e' <- eval e
     return $ Decl p x e'
evalDecl d = return d

evalDeclCek :: MonadFD4 m => Decl TTerm -> m (Decl TTerm)
evalDeclCek (Decl p x e) = 
  do e' <- evalCEK e
     return $ Decl p x e'
evalDeclCek d = return d

typecheckDecl :: MonadFD4 m => SDecl STerm -> m (Decl TTerm)
typecheckDecl decl = 
  do decl' <- elabDecl decl
     tcDecl decl' 

handleDecl ::  MonadFD4 m => SDecl STerm -> m ()
handleDecl d = do
        m <- getMode
        case m of
          Interactive -> do
              dd <- typecheckDecl d
              opt <- getOpt
              dd' <- if opt then optimizeDecl dd else return dd
              case dd' of
                (Decl p x tt) -> do
                  cek <- getCek
                  te <- if cek then evalCEK tt else eval tt
                  addDecl (Decl p x te)
                  prof <- getProf
                  when prof (do stats <- getStats
                                printFD4 (ppStats stats)
                                resetStats)
                (DeclTy p x ty) -> do
                  addTy x ty
          Typecheck -> do
              f <- getLastFile
              printFD4 ("Chequeando tipos de "++f)
              td <- typecheckDecl d
              addDecl' td
              opt <- getOpt
              td' <- if opt then optimizeDecl td else return td
              ppterm <- ppDecl td'
              printFD4 ppterm
          Eval -> do
              td <- typecheckDecl d
              opt <- getOpt
              td' <- if opt then optimizeDecl td else return td
              cek <- getCek
              ed <- if cek then evalDeclCek td' else evalDecl td'
              addDecl' ed
              prof <- getProf
              when prof (do stats <- getStats
                            printFD4 (ppStats stats)
                            resetStats)
          CC -> do
              td <- typecheckDecl d
              opt <- getOpt
              td' <- if opt then optimizeDecl td else return td
              cek <- getCek
              ed <- if cek then evalDeclCek td' else evalDecl td'
              addDecl' ed
              prof <- getProf
              when prof (do stats <- getStats
                            printFD4 (ppStats stats)
                            resetStats)
          _ -> return ()
  where addDecl' (DeclTy _ x ty) = addTy x ty
        addDecl' t = addDecl t


data Command = Compile CompileForm
             | PPrint String
             | Type String
             | Reload
             | Browse
             | Quit
             | Help
             | Noop

data CompileForm = CompileInteractive  String
                 | CompileFile         String

data InteractiveCommand = Cmd [String] String (String -> Command) String

-- | Parser simple de comando interactivos
interpretCommand :: String -> IO Command
interpretCommand x
  =  if ":" `isPrefixOf` x then
       do  let  (cmd,t')  =  break isSpace x
                t         =  dropWhile isSpace t'
           --  find matching commands
           let  matching  =  filter (\ (Cmd cs _ _ _) -> any (isPrefixOf cmd) cs) commands
           case matching of
             []  ->  do  putStrLn ("Comando desconocido `" ++ cmd ++ "'. Escriba :? para recibir ayuda.")
                         return Noop
             [Cmd _ _ f _]
                 ->  do  return (f t)
             _   ->  do  putStrLn ("Comando ambigüo, podría ser " ++
                                   intercalate ", " ([ head cs | Cmd cs _ _ _ <- matching ]) ++ ".")
                         return Noop

     else
       return (Compile (CompileInteractive x))

commands :: [InteractiveCommand]
commands
  =  [ Cmd [":browse"]      ""        (const Browse) "Ver los nombres en scope",
       Cmd [":load"]        "<file>"  (Compile . CompileFile)
                                                     "Cargar un programa desde un archivo",
       Cmd [":print"]       "<exp>"   PPrint          "Imprime un término y sus ASTs sin evaluarlo",
       Cmd [":reload"]      ""        (const Reload)         "Vuelve a cargar el último archivo cargado",
       Cmd [":type"]        "<exp>"   Type           "Chequea el tipo de una expresión",
       Cmd [":quit",":Q"]        ""        (const Quit)   "Salir del intérprete",
       Cmd [":help",":?"]   ""        (const Help)   "Mostrar esta lista de comandos" ]

helpTxt :: [InteractiveCommand] -> String
helpTxt cs
  =  "Lista de comandos:  Cualquier comando puede ser abreviado a :c donde\n" ++
     "c es el primer caracter del nombre completo.\n\n" ++
     "<expr>                  evaluar la expresión\n" ++
     "let <var> = <expr>      definir una variable\n" ++
     unlines (map (\ (Cmd c a _ d) ->
                   let  ct = intercalate ", " (map (++ if null a then "" else " " ++ a) c)
                   in   ct ++ replicate ((24 - length ct) `max` 2) ' ' ++ d) cs)

-- | 'handleCommand' interpreta un comando y devuelve un booleano
-- indicando si se debe salir del programa o no.
handleCommand ::  MonadFD4 m => Command  -> m Bool
handleCommand cmd = do
   s@GlEnv {..} <- get
   case cmd of
       Quit   ->  return False
       Noop   ->  return True
       Help   ->  printFD4 (helpTxt commands) >> return True
       Browse ->  do  printFD4 (unlines (reverse (nub (map declName glb))))
                      return True
       Compile c ->
                  do  case c of
                          CompileInteractive e -> compilePhrase e
                          CompileFile f        -> compileFile f
                      return True
       Reload ->  eraseLastFileDecls >> (getLastFile >>= compileFile) >> return True
       PPrint e   -> printPhrase e >> return True
       Type e    -> typeCheckPhrase e >> return True

compilePhrase ::  MonadFD4 m => String -> m ()
compilePhrase x = do
    dot <- parseIO "<interactive>" declOrTm x
    case dot of
      Left d  -> handleDecl d
      Right t -> handleTerm t

handleTerm ::  MonadFD4 m => STerm -> m ()
handleTerm t = do
         t' <- elab t
         s <- get
         tt <- tc t' (tyEnv s)
         cek <- getCek
         te <- if cek then evalCEK tt else eval tt
         ppte <- pp te
         printFD4 (ppte ++ " : " ++ ppTy (getTy tt))
         prof <- getProf
         when prof (do stats <- getStats
                       printFD4 (ppStats stats)
                       resetStats)

printPhrase   :: MonadFD4 m => String -> m ()
printPhrase x =
  do
    x' <- parseIO "<interactive>" tm x
    ex <- elab x'
    tyenv <- gets tyEnv
    tex <- tc ex tyenv
    t  <- case x' of
           (SV p f) -> fromMaybe tex <$> lookupDecl f
           _       -> return tex
    printFD4 "STerm:"
    printFD4 (show x')
    printFD4 "TTerm:"
    printFD4 (show t)

typeCheckPhrase :: MonadFD4 m => String -> m ()
typeCheckPhrase x = do
         t <- parseIO "<interactive>" tm x
         t' <- elab t
         s <- get
         tt <- tc t' (tyEnv s)
         let ty = getTy tt
         printFD4 (ppTy ty)
