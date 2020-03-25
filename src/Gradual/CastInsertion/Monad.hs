{-# OPTIONS_GHC -Wwarn #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE FunctionalDependencies     #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE BangPatterns #-}


module Gradual.CastInsertion.Monad (
  ToCore,
  runToCore,
  MonadUnique (..),
  HasDynFlags (..),
  HasModule (..),
  MonadThings (..),
  Debugger (..),
  getHEnv,
  freshId,
  symSortEnv,
  fTyConEnv,
  tyConEnv,
  lookupSymSort,
  insertSymSort,
  lookupLocalId,
  insertLocalId,
  lookupLocalExpr,
  lookupSType,
  tyconFTycon,
  ftyconTycon,
  withCore,
  withSubs,
  withTopVar,
  liftMaybe,
  checkSub,
  compareSpecTypes,
  printEnv
  ) where

import           Control.Monad.Reader
-- import           Control.Monad.State.Strict
import           Control.Monad.State.Lazy
import           CoreMonad                     (CoreM, SimplCount, errorMsgS,
                                                getHscEnv, putMsgS, runCoreM)
import           CoreSyn (RuleBase, CoreExpr)
import qualified Data.HashMap.Strict as M
import           Debug.Trace
import           DynFlags (HasDynFlags (..))
import           HscTypes (HscEnv, MonadThings (..))
import           Id (Id, mkLocalId)
import           Module                        (HasModule (..), Module,
                                                ModuleSet)
import           Name (Name, mkInternalName)
import           OccName (mkVarOcc)
import           Outputable (PrintUnqualified)
import           SrcLoc (SrcSpan, noSrcSpan)
import           TyCon (TyCon)
import           Type (Type)
import           UniqSupply (MonadUnique (..), UniqSupply)
import           Var

import           Language.Fixpoint.Solver       (solve)
import           Language.Fixpoint.Types.PrettyPrint (showpp)
import           Language.Fixpoint.Types hiding (SubC, SrcSpan, senv)
import qualified Language.Fixpoint.Types.Config as F
import           Language.Haskell.Liquid.Types
import           Language.Haskell.Liquid.Constraint.Types (CGInfo (..), CGEnv (..), SubC (..), FixSubC, CG (..))
import           Language.Haskell.Liquid.Constraint.Env (insertREnv, lookupREnv, fromListREnv)
import           Language.Haskell.Liquid.Constraint.Init (initEnv)
import           Language.Haskell.Liquid.Constraint.Split (splitC)
import           Language.Haskell.Liquid.Constraint.ToFixpoint (cgInfoFInfo, fixConfig)

newtype ToCore a = ToCore {
  unToCoreM :: ReaderT ToCoreInfo (StateT ToCoreState CoreM) a
  } deriving (Functor, Applicative, Monad, MonadState ToCoreState, MonadReader ToCoreInfo, MonadIO)

data ToCoreState
  = ToCoreState { to_core_ids :: SEnv Id
                , to_core_exprs :: SEnv CoreExpr
                , to_core_expr_sort :: SEnv Sort
                , to_core_tl_var :: Maybe Var
                , to_core_cginfo :: CGInfo
                }

data ToCoreInfo
  = ToCoreInfo { to_core_ftycons :: M.HashMap FTycon TyCon
               , to_core_tycons :: M.HashMap TyCon FTycon
               , to_core_cgenv :: CGEnv
               , to_core_specs :: REnv
               }

class Monad m => Debugger m where
  printMsg   :: String -> m ()
  printError :: String -> m ()

instance Debugger ToCore where
  printMsg = liftCore . printMsg
  printError = liftCore . printError

instance Debugger CoreM where
  printMsg = putMsgS
  printError = errorMsgS

instance MonadUnique ToCore where
  getUniqueSupplyM = liftCore getUniqueSupplyM

instance HasDynFlags ToCore where
  getDynFlags = liftCore getDynFlags

instance HasModule ToCore where
  getModule = liftCore getModule

instance MonadThings ToCore where
  lookupThing = liftCore . lookupThing

withTopVar :: Var -> ToCore a -> ToCore a
withTopVar x = withCore (updateTopVar x)

updateTopVar :: Var -> ToCoreState -> ToCoreState
updateTopVar x s = s {to_core_tl_var = Just x}

withCore :: (ToCoreState -> ToCoreState) -> ToCore a -> ToCore a
withCore f tc = ToCore $ ReaderT $ \r -> withStateT f $ flip runReaderT r $ unToCoreM tc

withSubs :: [(Symbol, Id)] -> [(Symbol, CoreExpr)] -> ToCore a -> ToCore a
withSubs subIds subExprs tc = do
  ids <- gets to_core_ids
  exprs <- gets to_core_exprs
  let ids' = fromListSEnv subIds
  let exprs' = fromListSEnv subExprs
  let uids = unionSEnv' ids ids'
  let uexprs = unionSEnv' exprs exprs'
  modify (\s -> s {to_core_ids = uids, to_core_exprs = uexprs})
  tc

liftCG :: CG a -> ToCore a
liftCG cg = ToCore $ ReaderT $ \r -> StateT $ \s -> let (a, t) = runState cg (to_core_cginfo s)
                                                    in pure (a, s {to_core_cginfo = t})

liftCore :: CoreM a -> ToCore a
liftCore cm = ToCore $ ReaderT $ \_ ->  StateT $ \s -> (, s) <$> cm

liftMaybe :: String -> Maybe a -> ToCore a
liftMaybe msg Nothing = fail msg
liftMaybe _ (Just x)  = pure x

getHEnv :: ToCore HscEnv
getHEnv = liftCore getHscEnv

symSortEnv :: ToCore (SEnv Sort)
symSortEnv = gets to_core_expr_sort

fTyConEnv :: ToCore (M.HashMap FTycon TyCon)
fTyConEnv = asks to_core_ftycons

tyConEnv :: ToCore (M.HashMap TyCon FTycon)
tyConEnv = asks to_core_tycons

-- addC :: SpecType -> SpecType -> ToCore ()
-- addC s1 s2
--   = do env <- asks to_core_specs
--        modify (\s -> s {to_core_cginfo =
--                         (let cgi = to_core_cginfo s
--                          in cgi {hsCs = (SubC env s1 s2) : (hsCs cgi)})})

getSubC :: SpecType -> SpecType -> ToCore (Maybe SubC)
getSubC s1 s2
  = do hsubs <- gets $ hsCs . to_core_cginfo
       case filter f hsubs of
         [subC] -> pure $ Just subC
         -- _      -> pure Nothing
         xs     -> do liftIO $ putStrLn $ showpp xs
                      liftIO $ putStrLn "Candidates"
                      liftIO $ putStrLn $ show s1
                      liftIO $ putStrLn $ show s2
                      fail $ "Can't find matching SubC, found: " ++ (show $ length xs)
  where
    f (SubC _ t1 t2) = compareSpecTypes s1 t1 && compareSpecTypes s2 t2

instance Show Cinfo where
  show = show . toFix

instance Eq a => Eq (UReft a) where
  r1 == r2 = (ur_reft r1) == (ur_reft r2)


checkSub :: SpecType -> SpecType -> ToCore Bool
checkSub s1 s2
  | isTrivial s2 = pure True
  | otherwise
  = do cgi      <- gets to_core_cginfo
       env      <- asks to_core_cgenv
       topVar   <- gets to_core_tl_var
       let env' =  env {cgVar = topVar}
       let sC   =  SubC env' s1 s2
       -- let sC'  =  ungrad sC
       fixSubCs <- liftCG $ splitC sC
       let cgi' =  singleConstraint fixSubCs cgi
       let ghci =  ghcI cgi
       let fcfg =  fixConfig (target ghci) (getConfig ghci)
       -- let fcfg' = fcfg {F.gradual=False, F.ginteractive=False}
       finfo    <- liftIO $ cgInfoFInfo ghci cgi'
       res      <- liftIO $ solve fcfg finfo
       -- liftIO $ putStrLn "Candidates"
       -- liftIO $ print $ senv sC
       -- liftIO $ print $ lhs sC
       -- liftIO $ print $ rhs sC
       -- liftIO $ print $ res
       -- pure $ isSafe res
       pure False


stripST :: SpecType -> SpecType
stripST (RAllP _ s) = stripST s
stripST (RAllS _ s) = stripST s
stripST (RRTy _ _ _ s) = stripST s
stripST (RAllE _ _ s) = stripST s
stripST (REx _ _ s) = stripST s
stripST s = s

compareSpecTypes :: SpecType -> SpecType -> Bool
compareSpecTypes s1 s2 = compareSpecTypes' (stripST s1) (stripST s2)

-- Needs to replace with proper subtyping checking.
compareSpecTypes' :: SpecType -> SpecType -> Bool
compareSpecTypes' (RVar _ r1) (RVar _ r2) = r1 =?= r2
compareSpecTypes' (RFun _ i1 o1 r1) (RFun _ i2 o2 r2) = compareSpecTypes i1 i2 && compareSpecTypes o1 o2 && r1 =?= r2
compareSpecTypes' (RAllT _ s1) (RAllT _ s2) = compareSpecTypes s1 s2
compareSpecTypes' (RAllP _ s1) (RAllP _ s2) = compareSpecTypes s1 s2
compareSpecTypes' (RAllS _ s1) (RAllS _ s2) = compareSpecTypes s1 s2
compareSpecTypes' (RApp _ args1 _ r1) (RApp _ args2 _ r2) = r1 =?= r2 && and (zipWith compareSpecTypes args1 args2)
compareSpecTypes' (RAllE _ a1 s1) (RAllE _ a2 s2) = compareSpecTypes a1 a2 && compareSpecTypes s1 s2
compareSpecTypes' (REx _ a1 t1) (REx _ a2 t2) = compareSpecTypes a1 a2 && compareSpecTypes t1 t2
compareSpecTypes' (RExprArg l1) (RExprArg l2) = l1 == l2
compareSpecTypes' (RAppTy a1 re1 r1) (RAppTy a2 re2 r2) = r1 =?= r2 && compareSpecTypes a1 a2 && compareSpecTypes re1 re2
compareSpecTypes' (RRTy _ r1 _ t1) (RRTy _ r2 _ t2) = r1 =?= r2 && compareSpecTypes t1 t2
compareSpecTypes' (RHole r1) (RHole r2) = r1 =?= r2
compareSpecTypes' s1 s2 = False

myTrace :: Show a =>  String -> a -> a -> b -> b
myTrace name s1 s2 = trace (name ++ ":\n" ++ show s1 ++ "\n" ++ show s2)

compareExpr :: Expr -> Expr -> Bool
compareExpr (PGrad k1 _ i1 e1) (PGrad k2 _ i2 e2)
  = k1 == k2 && i1 == i2 && e1 == e2
compareExpr e1 e2 = e1 == e2

(=?=) :: RReft -> RReft -> Bool
(=?=) (MkUReft (Reft r1) _ _) (MkUReft (Reft r2) _ _) = cmp r1 r2
  where
    cmp (s1, e1) (s2, e2) = compareExpr e1 e2

singleConstraint :: [FixSubC] -> CGInfo -> CGInfo
singleConstraint fixSubC cgi
  = cgi { fixCs  = fixSubC
        , fixWfs = []
        }

defaultToCoreState :: CGInfo -> ToCoreState
defaultToCoreState cgi
  = ToCoreState { to_core_ids       = mempty
                , to_core_exprs     = mempty
                , to_core_expr_sort = mempty
                , to_core_tl_var    = Nothing
                , to_core_cginfo  = cgi
                }

defaultToCoreInfo :: CGInfo -> ToCoreInfo
defaultToCoreInfo cgi
  = ToCoreInfo { to_core_ftycons = mempty
               , to_core_tycons  = mempty
               , to_core_specs   = initSpecs cgi
               , to_core_cgenv   = cge
               }
               where
                 cge = evalState (initEnv $ ghcI cgi) cgi

initSpecs :: CGInfo -> REnv
initSpecs cgi = addTopMain $ fromListREnv globals locals
  where
    globals = renvs reGlobal
    locals = renvs reLocal
    renvs f = concat $ fmap (cgiToSpecs f) [renv, grtys]
    toMaps f g = fmap (f . g . senv) . hsCs
    cgiToSpecs f g = concat $ M.toList <$> toMaps f g cgi

addTopMain :: REnv -> REnv
addTopMain renv = case lookupREnv (symbol "Main.main") renv of
  Nothing -> renv
  Just spec -> insertREnv (symbol ":Main.main") spec renv

-- getSpecs :: CGInfo -> [(Symbol, SpecType)]
-- getSpecs cg = concat $ localSpecs ++ globalSpecs
--   where
--     localSpecs = cgToSpecs reLocal
--     globalSpecs = cgToSpecs reGlobal
--     toMaps f = fmap (f . renv . senv) . hsCs
--     cgToSpecs f = M.toList <$> toMaps f cg

lookupSType :: Symbolic a => a -> ToCore SpecType
lookupSType x = do
  refts <- asks to_core_specs
  case lookupREnv (symbol x) refts of
    Nothing   -> fail $ "Identifier " ++ show (symbol x) ++ " not in scope."
    Just spec -> pure spec


instance Show REnv where
  show (REnv g l) = unlines ["REnv", "ReGlobal", show g, "ReLocal", show l]

insertSymSort :: Symbolic a => a -> Sort -> ToCore ()
insertSymSort name idx
  = modify (\s -> s {to_core_expr_sort =
                     insertSEnv (symbol name) idx (to_core_expr_sort s)})

lookupSymSort :: Symbolic a => a -> ToCore (Maybe Sort)
lookupSymSort name
  = gets (\s -> lookupSEnv (symbol name) $ to_core_expr_sort s)

insertLocalId :: Symbolic a => a -> Id -> ToCore ()
insertLocalId name idx
  = modify (\s -> s {to_core_ids =
                     insertSEnv (symbol name) idx (to_core_ids s)})

lookupLocalId :: Symbolic a => a -> ToCore (Maybe Id)
lookupLocalId name =
  gets (\s -> lookupSEnv (symbol name) $ to_core_ids s)

lookupLocalExpr :: Symbolic a => a -> ToCore (Maybe CoreExpr)
lookupLocalExpr name =
  gets (\s -> lookupSEnv (symbol name) $ to_core_exprs s)

tyconFTycon :: FTycon -> ToCore (Maybe TyCon)
tyconFTycon tc = asks (\s -> M.lookup tc $ to_core_ftycons s)

ftyconTycon :: TyCon -> ToCore (Maybe FTycon)
ftyconTycon tc = asks (\s -> M.lookup tc $ to_core_tycons s)

freshId :: String -> Type -> ToCore Id
freshId s ty = do
  uniq <- getUniqueM
  let occ = mkVarOcc $ s ++ "#" ++ show uniq
  let name = mkInternalName uniq occ noSrcSpan
  pure $ mkLocalId name ty

runToCoreDef :: CGInfo -> TCEmb TyCon -> ToCore a -> CoreM a
runToCoreDef cgi tc
  = flip evalStateT (defaultToCoreState cgi) . flip runReaderT info . unToCoreM
  where
    info = (defaultToCoreInfo cgi) { to_core_tycons = tc }

runToCore :: HscEnv
          -> RuleBase
          -> UniqSupply
          -> Module
          -> ModuleSet
          -> PrintUnqualified
          -> SrcSpan
          -> CGInfo
          -> TCEmb TyCon
          -> ToCore a
          -> IO (a, SimplCount)
runToCore he rb us mod ms pu ss cgi tc
  = runCoreM he rb us mod ms pu ss . runToCoreDef cgi tc


instance HasGradual a => HasGradual (UReft a) where
  isGradual = isGradual . ur_reft
  gVars = gVars . ur_reft
  ungrad = fmap ungrad

instance HasGradual SpecType where
  isGradual (RVar _ r) = isGradual r
  isGradual (RFun _ r i o) = isGradual r || isGradual i || isGradual o
  isGradual (RAllT _ b) = isGradual b
  isGradual (RAllP _ b) = isGradual b
  isGradual (RAllS _ b) = isGradual b
  isGradual (RApp _ args _ r) = any isGradual args || isGradual r
  isGradual (RAllE _ args ty) = isGradual args || isGradual ty
  isGradual (REx _ args ty) = isGradual args || isGradual ty
  isGradual (RExprArg lexpr) = isGradual lexpr
  isGradual (RAppTy arg res r) = any isGradual [arg, res] || isGradual r
  isGradual (RRTy env ref _ ty) =
    any (isGradual . snd) env || isGradual ref || isGradual ty
  isGradual (RHole r) = isGradual r

  gVars (RVar _ r)          = gVars r
  gVars (RFun _ r i o)      =  gVars r ++ gVars i ++ gVars o
  gVars (RAllT _ b)         = gVars b
  gVars (RAllP _ b)         = gVars b
  gVars (RAllS _ b)         = gVars b
  gVars (RApp _ args _ r)   = concat (gVars <$> args) ++ gVars r
  gVars (RAllE _ args ty)   = gVars args ++ gVars ty
  gVars (REx _ args ty)     = gVars args ++ gVars ty
  gVars (RExprArg lexpr)    = gVars lexpr
  gVars (RAppTy arg res r)  = concat (gVars <$> [arg, res]) ++ gVars r
  gVars (RRTy env ref _ ty) = (env >>= gVars . snd) ++ gVars ref ++ gVars ty
  gVars (RHole r)           = gVars r

  ungrad (RVar x r) = RVar x $ ungrad r
  ungrad (RFun x r i o) = RFun x (ungrad r) (ungrad i) (ungrad o)
  ungrad (RAllT x b) = RAllT x $ ungrad b
  ungrad (RAllP x b) = RAllP x $ ungrad b
  ungrad (RAllS x b) = RAllS x $ ungrad b
  ungrad (RApp c args pargs r) = RApp c (ungrad <$> args) pargs (ungrad r)
  ungrad (RAllE x args ty) = RAllE x (ungrad args) (ungrad ty)
  ungrad (REx x args ty) = REx x (ungrad args) (ungrad ty)
  ungrad (RExprArg lexpr) = RExprArg (ungrad lexpr)
  ungrad (RAppTy arg res r) = RAppTy (ungrad arg) (ungrad res) (ungrad r)
  ungrad (RRTy env ref o ty) =
    RRTy ((fmap . fmap) ungrad env) (ungrad ref) o (ungrad ty)
  ungrad (RHole r) = RHole $ ungrad r

instance HasGradual SubC where
  isGradual (SubC env lhs rhs) = isGradual env || isGradual lhs || isGradual rhs
  gVars (SubC env lhs rhs) = gVars env ++ gVars lhs ++ gVars rhs
  ungrad (SubC env lhs rhs) = SubC (ungrad env) (ungrad lhs) (ungrad rhs)

instance HasGradual CGEnv where
  isGradual cge
    =  (isGradual $ renv cge)
    || (isGradual $ grtys cge)
    || (isGradual $ assms cge)
    || (isGradual $ intys cge)

  gVars cge
    =  (gVars $ renv cge)
    ++ (gVars $ grtys cge)
    ++ (gVars $ assms cge)
    ++ (gVars $ intys cge)

  ungrad cge
    = cge { renv  = ungrad $ renv cge
          , grtys = ungrad $ grtys cge
          , assms = ungrad $ assms cge
          , intys = ungrad $ intys cge
          }

instance HasGradual REnv where
  isGradual (REnv rg rl) = any isGradual $ M.elems rg ++ M.elems rl
  gVars (REnv rg rl) = gVars $ M.elems rg ++ M.elems rl
  ungrad (REnv rg rl) = REnv (ungrad <$> rg) (ungrad <$> rl)

instance HasGradual a => HasGradual [a] where
  isGradual = any isGradual
  gVars = (>>= gVars)
  ungrad = fmap ungrad

instance HasGradual a => HasGradual (Located a) where
  isGradual = isGradual . val
  gVars = gVars . val
  ungrad l = l { val = ungrad (val l) }


printEnv :: ToCore ()
printEnv = do
  ids <- gets to_core_ids
  exprs <- gets to_core_exprs
  printMsg "IDS"
  printMsg $ show ids
  printMsg "Expr"
  printMsg $ show (fmap fst . toListSEnv $ exprs)
