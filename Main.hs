module Main where

import Control.Monad
import Control.Monad.Fail (MonadFail)
import Control.Monad.IO.Class
import Data.Function
import Data.List
import Data.Maybe
import Data.Map (Map)
import qualified Data.Map as Map
import System.Console.GetOpt
import System.Environment

import qualified Language.Haskell.Exts.SrcLoc     as Hs
import qualified Language.Haskell.Exts.Syntax     as Hs
import qualified Language.Haskell.Exts.Pretty     as Hs
import qualified Language.Haskell.Exts.Parser     as Hs
import qualified Language.Haskell.Exts.ExactPrint as Hs
import qualified Language.Haskell.Exts.Comments   as Hs

import Agda.Main (runAgda)
import Agda.Compiler.Backend
import Agda.Compiler.Common
import Agda.Interaction.BasicOps
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Pretty hiding (pretty)
import Agda.Syntax.Common
import Agda.Syntax.Literal
import Agda.Syntax.Internal
import Agda.Syntax.Position
import Agda.Syntax.Translation.ConcreteToAbstract
import Agda.TheTypeChecker
import Agda.TypeChecking.Rules.Term (isType_)
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute hiding (sort)
import Agda.TypeChecking.Telescope
import Agda.Interaction.CommandLine (withCurrentFile)
import Agda.Utils.Lens
import Agda.Utils.Pretty (prettyShow)
import qualified Agda.Utils.Pretty as P
import Agda.Utils.FileName
import Agda.Utils.List
import Agda.Utils.Impossible
import Agda.Utils.Maybe.Strict (toLazy, toStrict)

data Options = Options { }

defaultOptions :: Options
defaultOptions = Options{}

pragmaName :: String
pragmaName = "AGDA2HS"

type Env         = ()
type ModuleEnv   = ()
type ModuleRes   = ()
type CompiledDef = [(Range, [Hs.Decl ()])]

backend :: Backend' Options Env ModuleEnv ModuleRes CompiledDef
backend = Backend'
  { backendName           = "agda2hs"
  , backendVersion        = Just "0.1"
  , options               = defaultOptions
  , commandLineFlags      = []
  , isEnabled             = \ _ -> True
  , preCompile            = \ _ -> return ()
  , postCompile           = \ _ _ _ -> return ()
  , preModule             = \ _ _ _ _ -> return (Recompile ())
  , postModule            = writeModule
  , compileDef            = compile
  , scopeCheckingSuffices = False
  , mayEraseType          = \ _ -> return True
  }

showTCM :: PrettyTCM a => a -> TCM String
showTCM x = show <$> prettyTCM x

compile :: Env -> ModuleEnv -> IsMain -> Definition -> TCM CompiledDef
compile _ _ _ def = getUniqueCompilerPragma pragmaName (defName def) >>= \ case
  Nothing -> return []
  Just _  -> compile' def

compile' :: Definition -> TCM CompiledDef
compile' def =
  case theDef def of
    Function{} -> compileFun r hsName def
    Datatype{} -> compileData r hsName def
    _          -> return []
  where x = qnameName $ defName def
        r = nameBindingSite x
        hsName = prettyShow x

compileData :: Range -> String -> Definition -> TCM CompiledDef
compileData r d def = do
  case theDef def of
    Datatype{dataPars = n, dataIxs = 0, dataCons = cs} -> do
      TelV tel _ <- telViewUpTo n (defType def)
      addContext tel $ do
        builtins <- getBuiltins
        let params = teleArgs tel :: [Arg Term]
        pars <- mapM (showTCM . unArg) $ filter visible params
        cs   <- mapM (compileConstructor builtins params) cs
        let hd   = foldl (\ h p -> Hs.DHApp () h (Hs.UnkindedVar () $ hsName p))
                         (Hs.DHead () (hsName d)) pars
            code = [Hs.DataDecl () (Hs.DataType ()) Nothing hd cs []]
        return [(r, code)]
    _ -> __IMPOSSIBLE__

compileConstructor :: Builtins -> [Arg Term] -> QName -> TCM (Hs.QualConDecl ())
compileConstructor builtins params c = do
  ty <- (`piApplyM` params) . defType =<< getConstInfo c
  TelV tel _ <- telView ty
  c <- showTCM c
  args <- compileConstructorArgs builtins tel
  return $ Hs.QualConDecl () Nothing Nothing $ Hs.ConDecl () (hsName c) args

compileConstructorArgs :: Builtins -> Telescope -> TCM [Hs.Type ()]
compileConstructorArgs _ EmptyTel = return []
compileConstructorArgs builtins (ExtendTel a tel)
  | visible a, NoAbs _ tel <- reAbs tel = do
    (:) <$> compileType builtins (unEl $ unDom a) <*> compileConstructorArgs builtins tel
compileConstructorArgs _ tel = genericDocError =<< text "Bad constructor args:" <?> prettyTCM tel

compileClause :: String -> Clause -> TCM (Hs.Match ())
compileClause x Clause{clauseTel       = tel,
                       namedClausePats = ps,
                       clauseBody      = body } =
  addContext tel $ do
    builtins <- getBuiltins
    ps   <- compilePats builtins ps
    body <- maybe (return $ Hs.Var () $ Hs.UnQual () (hsName "undefined")) (compileTerm builtins) body
    -- TODO: infix match
    return $ Hs.Match () (hsName x) ps (Hs.UnGuardedRhs () body) Nothing

isInfix :: String -> Maybe String
isInfix ('_' : f) = do
  (op, '_') <- initLast f
  return op
isInfix _ = Nothing

hsName :: String -> Hs.Name ()
hsName x
  | Just op <- isInfix x = Hs.Symbol () op
  | otherwise            = Hs.Ident () x

hsQName :: Builtins -> QName -> TCM (Hs.QName ())
hsQName builtins f
  | Just p <- Map.lookup f builtins = return $ compilePrim p
  | otherwise = do
    s <- showTCM f
    return $
      case break (== '.') $ reverse s of
        (_, "")        -> Hs.UnQual () (hsName s)
        (fr, _ : mr) -> Hs.Qual () (Hs.ModuleName () $ reverse mr) (hsName $ reverse fr)

compilePrim :: Prim -> Hs.QName ()
compilePrim Nat  = Hs.UnQual () (hsName "Integer")
compilePrim List = Hs.Special () (Hs.ListCon ())
compilePrim Unit = Hs.Special () (Hs.UnitCon ())
compilePrim Cons = Hs.Special () (Hs.Cons ())
compilePrim Nil  = Hs.Special () (Hs.ListCon ())

compilePats :: Builtins -> NAPs -> TCM [Hs.Pat ()]
compilePats builtins ps = mapM (compilePat builtins . namedArg) $ filter visible ps

compilePat :: Builtins -> DeBruijnPattern -> TCM (Hs.Pat ())
compilePat builtins p@(VarP _ _)  = Hs.PVar () . hsName <$> showTCM p
compilePat builtins (ConP h _ ps) = do
  ps <- compilePats builtins ps
  c <- hsQName builtins (conName h)
  return $ pApp c ps
-- TODO: LitP
compilePat _ p = genericDocError =<< text "bad pattern:" <?> prettyTCM p

pApp :: Hs.QName () -> [Hs.Pat ()] -> Hs.Pat ()
pApp c@(Hs.UnQual () (Hs.Symbol () _)) [p, q] = Hs.PInfixApp () p c q
pApp c@(Hs.Special () Hs.Cons{}) [p, q] = Hs.PInfixApp () p c q
pApp c ps = Hs.PApp () c ps

eApp :: Hs.Exp () -> [Hs.Exp ()] -> Hs.Exp ()
eApp f (a : b : as) | Just op <- isOp f = foldl (Hs.App ()) (Hs.InfixApp () a op b) as
  where isOp (Hs.Var _ x) = Hs.QVarOp () <$> isOp' x
        isOp (Hs.Con _ c) = Hs.QConOp () <$> isOp' c
        isOp' x@(Hs.UnQual () (Hs.Symbol () _)) = Just x
        isOp' c@(Hs.Special () Hs.Cons{}) = Just c
        isOp' _ = Nothing
eApp f es = foldl (Hs.App ()) f es

tApp :: Hs.Type () -> [Hs.Type ()] -> Hs.Type ()
tApp (Hs.TyCon () (Hs.Special () Hs.ListCon{})) [a] = Hs.TyList () a
tApp t vs = foldl (Hs.TyApp ()) t vs

compileTerm :: Builtins -> Term -> TCM (Hs.Exp ())
compileTerm builtins v =
  case unSpine v of
    Var x es   -> (`app` es) . Hs.Var () . Hs.UnQual () . hsName =<< showTCM (Var x [])
    Def f es   -> (`app` es) . Hs.Var () =<< hsQName builtins f
    Con h i es -> (`app` es) . Hs.Con () =<< hsQName builtins (conName h)
    Lit (LitNat n) -> return $ Hs.Lit () $ Hs.Int () n (show n)
    t -> genericDocError =<< text "bad term:" <?> prettyTCM t
  where
    app :: Hs.Exp () -> Elims -> TCM (Hs.Exp ())
    app hd es = do
      let Just args = allApplyElims es
      args <- mapM (compileTerm builtins . unArg) $ filter visible args
      return $ eApp hd args

paren True  s = "(" ++ s ++ ")"
paren False s = s

data Prim = Nat | List | Unit | Cons | Nil
  deriving (Show, Eq)

type Builtins = Map QName Prim

getBuiltins :: TCM Builtins
getBuiltins = Map.fromList . concat <$> mapM getB
                [ (builtinNat,  Nat)
                , (builtinList, List)
                , (builtinUnit, Unit)
                , (builtinCons, Cons)
                , (builtinNil,  Nil)
                ]
  where
    getB (b, t) = getBuiltin' b >>= \ case
      Nothing          -> return []
      Just (Def q _)   -> return [(q, t)]
      Just (Con c _ _) -> return [(conName c, t)]
      Just _           -> __IMPOSSIBLE__

compileType :: Builtins -> Term -> TCM (Hs.Type ())
compileType builtins t = do
  t <- reduce t
  case t of
    Pi a b | hidden a -> underAbstraction a b (compileType builtins . unEl)
             -- Hidden Pi means Haskell forall
    Pi a (NoAbs _ b) | visible a -> do
      hsA <- compileType builtins (unEl $ unDom a)
      hsB <- compileType builtins (unEl b)
      return $ Hs.TyFun () hsA hsB
    Def f es | Just args <- allApplyElims es -> do
      vs <- mapM (compileType builtins . unArg) $ filter visible args
      f <- hsQName builtins f
      return $ tApp (Hs.TyCon () f) vs
    Var x es | Just args <- allApplyElims es -> do
      vs <- mapM (compileType builtins . unArg) $ filter visible args
      x  <- hsName <$> showTCM (Var x [])
      return $ tApp (Hs.TyVar () x) vs
    t -> genericDocError =<< text "Bad Haskell type:" <?> prettyTCM t

compileFun :: Range -> String -> Definition -> TCM CompiledDef
compileFun r x def = do
  builtins <- getBuiltins
  ty <- compileType builtins (unEl $ defType def)
  cs <- mapM (compileClause x) funClauses
  let code = [Hs.TypeSig () [hsName x] ty, Hs.FunBind () cs]
  return [(r, code)]
  where
    Function{..} = theDef def

type Code = (Hs.Module Hs.SrcSpanInfo, [Hs.Comment])

getForeignPragmas :: TCM [(Range, Code)]
getForeignPragmas = do
  pragmas <- fromMaybe [] . Map.lookup pragmaName . iForeignCode <$> curIF
  reverse <$> mapM getCode pragmas
  where
    getCode :: ForeignCode -> TCM (Range, Code)
    getCode (ForeignCode r code) = do
          let Just file = fmap filePath $ toLazy $ rangeFile r
              pmode = Hs.defaultParseMode { Hs.parseFilename     = file,
                                            Hs.ignoreLinePragmas = False }
              line = case posLine <$> rStart r of
                       Just l  -> "{-# LINE " ++ show l ++ show file ++ " #-}\n"
                       Nothing -> ""
          case Hs.parseWithComments pmode (line ++ code) of
            Hs.ParseOk m           -> return (r, m)
            Hs.ParseFailed loc msg -> setCurrentRange (srcLocToRange loc) $ genericError msg

srcSpanToRange :: Hs.SrcSpan -> Range
srcSpanToRange (Hs.SrcSpan file l1 c1 l2 c2) =
  intervalToRange (toStrict $ Just $ mkAbsolute file) $ Interval (pos l1 c1) (pos l2 c2)
  where pos l c = Pn () 0 (fromIntegral l) (fromIntegral c)

srcLocToRange :: Hs.SrcLoc -> Range
srcLocToRange (Hs.SrcLoc file l c) = srcSpanToRange (Hs.SrcSpan file l c l c)

type Block = (Range, [String])

renderComment (Hs.Comment True  _ s) = "{-" ++ s ++ "-}"
renderComment (Hs.Comment False _ s) = "--" ++ s

sortRanges :: [(Range, a)] -> [a]
sortRanges = map snd . sortBy (compare `on` rLine . fst)

rLine :: Range -> Int
rLine r = fromIntegral $ fromMaybe 0 $ posLine <$> rStart r

renderBlocks :: [Block] -> String
renderBlocks = unlines . map unlines . sortRanges . filter (not . null . snd)

defBlock :: CompiledDef -> [Block]
defBlock def = [ (r, map pp ds) | (r, ds) <- def ]

codePragmas :: [(Range, Code)] -> [Block]
codePragmas code = [ (r, map pp ps) | (r, (Hs.Module _ _ ps _ _, _)) <- code ]

codeBlocks :: [(Range, Code)] -> [Block]
codeBlocks code = [(r, [uncurry Hs.exactPrint $ moveToTop $ noPragmas mcs]) | (r, mcs) <- code, nonempty mcs]
  where noPragmas (Hs.Module l h _ is ds, cs) = (Hs.Module l h [] is ds, cs)
        nonempty (Hs.Module _ _ _ is ds, cs) = not $ null is && null ds && null cs

moveToTop :: Hs.Annotated ast => (ast Hs.SrcSpanInfo, [Hs.Comment]) -> (ast Hs.SrcSpanInfo, [Hs.Comment])
moveToTop (x, cs) = (subtractLine l <$> x, [ Hs.Comment b (sub l r) str | Hs.Comment b r str <- cs ])
  where l = Hs.startLine (Hs.ann x) - 1
        subtractLine :: Int -> Hs.SrcSpanInfo -> Hs.SrcSpanInfo
        subtractLine l (Hs.SrcSpanInfo s ss) = Hs.SrcSpanInfo (sub l s) (map (sub l) ss)

        sub :: Int -> Hs.SrcSpan -> Hs.SrcSpan
        sub l (Hs.SrcSpan f l0 c0 l1 c1) = Hs.SrcSpan f (l0 - l) c0 (l1 - l) c1

pp :: Hs.Pretty a => a -> String
pp = Hs.prettyPrintWithMode Hs.defaultMode{ Hs.spacing = False }

writeModule :: Env -> ModuleEnv -> IsMain -> ModuleName -> [CompiledDef] -> TCM ModuleRes
writeModule _ _ isMain m defs0 = do
  code <- getForeignPragmas
  let defs = concatMap defBlock defs0 ++ codeBlocks code
  unless (null code && null defs) $ liftIO $ do
    putStr $ renderBlocks $ codePragmas code
    putStrLn $ "module " ++ prettyShow m ++ " where\n"
    putStr $ renderBlocks defs
    -- putStr $ renderBlocks defs

main = runAgda [Backend backend]

