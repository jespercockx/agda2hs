module Main where

import System.Console.GetOpt

import qualified Language.Haskell.Exts.Syntax as Hs
import qualified Language.Haskell.Exts.Build as Hs
import qualified Language.Haskell.Exts.Parser as Hs
import qualified Language.Haskell.Exts.Extension as Hs

import Agda.Main
import Agda.Compiler.Backend
import Agda.Compiler.Common ( curIF )
import Agda.TypeChecking.Monad.Imports ( getImports )

import Agda2Hs.Compile
import Agda2Hs.Compile.Types
import Agda2Hs.Render

defaultOptions :: Options
defaultOptions = Options{ optOutDir = ".", optExtensions = [] }

outdirOpt :: Monad m => FilePath -> Options -> m Options
outdirOpt dir opts = return opts{ optOutDir = dir }

extensionOpt :: Monad m => String -> Options -> m Options
extensionOpt ext opts = return opts{ optExtensions = Hs.parseExtension ext : optExtensions opts }

backend :: Backend' Options Options ModuleEnv ModuleRes Definition
backend = Backend'
  { backendName           = "agda2hs"
  , backendVersion        = Just "0.1"
  , options               = defaultOptions
  , commandLineFlags      = [ Option ['o'] ["out-dir"] (ReqArg outdirOpt "DIR")
                              "Write Haskell code to DIR. Default: ."
                            , Option ['X'] [] (ReqArg extensionOpt "EXTENSION")
                              "Enable Haskell language EXTENSION. Affects parsing of Haskell code in FOREIGN blocks."
                            ]
  , isEnabled             = \ _ -> True
  , preCompile            = return
  , postCompile           = compile
  , preModule             = preModule'
  , postModule            = postModule'
  , compileDef            = \ _ _ _ def -> return def
  , scopeCheckingSuffices = False
  , mayEraseType          = \ _ -> return True
  }

preModule' :: Options -> IsMain -> ModuleName -> Maybe FilePath -> TCM (Recompile ModuleEnv ModuleRes)
preModule' _ _ m _ = do
  iscope  <- iInsideScope <$> curIF
  return $ Recompile (m, iscope)

postModule' :: Options -> ModuleEnv -> IsMain -> ModuleName -> [Definition] -> TCM ModuleRes
postModule' _ (_,iscope) ismain _ defs = do
  imports <- getImports
  return $ ModuleRes ismain imports iscope defs

main = runAgda [Backend backend]
