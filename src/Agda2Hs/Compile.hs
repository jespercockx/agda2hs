module Agda2Hs.Compile where

import Control.Monad.Reader ( ReaderT(runReaderT) )
import Control.Monad.State

import Data.Map ( Map )
import qualified Data.Map as Map
import Data.Maybe
import Data.Set ( Set )
import qualified Data.Set as Set

import Agda.Compiler.Backend
import Agda.TypeChecking.Pretty
import Agda.Utils.Impossible
import Agda.Utils.List

import Agda2Hs.Compile.Definition ( compileDefinition )
import Agda2Hs.Compile.Types
import Agda2Hs.Pragma
import Agda2Hs.Render

initCompileEnv :: CompileEnv
initCompileEnv = CompileEnv
  { minRecordName = Nothing
  , isCompilingInstance = False
  }

runC :: C a -> TCM a
runC m = runReaderT m initCompileEnv

-- Get a list of all dependencies of the given module in dependency order.
-- The given module itself will be the final element of the list.
-- Implementation is inspired by `doCompile'` in Agda.Compiler.Common
getDependencies :: Map ModuleName ModuleRes -> ModuleName -> [ModuleName]
getDependencies deps m = evalState (go [] m) Set.empty
  where
    go :: [ModuleName] -> ModuleName -> State (Set ModuleName) [ModuleName]
    go ms m = do
      alreadyDone <- gets $ Set.member m
      if alreadyDone then return ms else do
        let imps = Set.toList $ modImports $ Map.findWithDefault __IMPOSSIBLE__ m deps
        modify $ Set.insert m
        foldM go (m:ms) imps


-- Main compile function
------------------------

compile :: Options -> IsMain -> Map ModuleName ModuleRes -> TCM ()
compile opts _ mods = runC $ do
  let main = fst $ headWithDefault __IMPOSSIBLE__
                 $ filter ((== IsMain) . modIsMain . snd)
                 $ Map.toList mods
      ms = getDependencies mods main

  forM_ ms $ \m -> withCurrentModule m $ do
    let ModuleRes{..} = fromMaybe __IMPOSSIBLE__ $ Map.lookup m mods
    liftTCM $ setScope modScope
    compiledDefs <- forM modDefinitions compileDefinition
    liftTCM $ writeModule opts m compiledDefs
