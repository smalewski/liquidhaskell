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
  tyconFTycon,
  ftyconTycon,
  withCore,
  withSubs
  ) where

import           Control.Monad.Reader
import           Control.Monad.State.Strict
import           CoreMonad                     (CoreM, SimplCount, errorMsgS,
                                                getHscEnv, putMsgS, runCoreM)
import           CoreSyn (RuleBase)
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

import           Language.Fixpoint.Types       (SEnv, Symbolic (..), emptySEnv, Sort,
                                                insertSEnv, lookupSEnv, Symbol, TCEmb, FTycon,
                                                fromListSEnv, unionSEnv')
import           Language.Haskell.Liquid.Types ()
import           Language.Haskell.Liquid.Constraint.Types (CGInfo (..))

newtype ToCore a = ToCore {
  unToCoreM :: ReaderT ToCoreInfo (StateT ToCoreState CoreM) a
  } deriving (Functor, Applicative, Monad, MonadState ToCoreState, MonadReader ToCoreInfo, MonadIO)

data ToCoreState = ToCoreState {
  to_core_ids :: SEnv Id,
  to_core_expr_sort :: SEnv Sort
  } deriving (Show)

data ToCoreInfo = ToCoreInfo {
  to_core_ftycons :: M.HashMap FTycon TyCon,
  to_core_tycons :: M.HashMap TyCon FTycon,
  to_core_cginfo :: CGInfo
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

withCore :: (ToCoreState -> ToCoreState) -> ToCore a -> ToCore a
withCore f tc = ToCore $ ReaderT $ \r -> withStateT f $ flip runReaderT r $ unToCoreM tc

withSubs :: [(Symbol, Id)] -> ToCore a -> ToCore a
withSubs subs tc = do
  ids <- gets to_core_ids
  let ids' = fromListSEnv subs
  let uids = unionSEnv' ids ids'
  modify (\s -> s {to_core_ids = uids})
  tc

liftCore :: CoreM a -> ToCore a
liftCore cm = ToCore $ ReaderT $ \_ ->  StateT $ \s -> (, s) <$> cm

getHEnv :: ToCore HscEnv
getHEnv = liftCore getHscEnv

symSortEnv :: ToCore (SEnv Sort)
symSortEnv = gets to_core_expr_sort

fTyConEnv :: ToCore (M.HashMap FTycon TyCon)
fTyConEnv = asks to_core_ftycons

tyConEnv :: ToCore (M.HashMap TyCon FTycon)
tyConEnv = asks to_core_tycons

defaultToCoreState :: ToCoreState
defaultToCoreState = ToCoreState {to_core_ids = mempty,
                                  to_core_expr_sort = mempty}

defaultToCoreInfo :: CGInfo -> ToCoreInfo
defaultToCoreInfo cgi = ToCoreInfo {to_core_ftycons = mempty,
                                    to_core_tycons = mempty,
                                    to_core_cginfo = cgi}

insertSymSort :: Symbolic a => a -> Sort -> ToCore ()
insertSymSort name idx =
  modify (\s -> s {to_core_expr_sort = insertSEnv (symbol name) idx (to_core_expr_sort s)})

lookupSymSort :: Symbolic a => a -> ToCore (Maybe Sort)
lookupSymSort name = gets (\s -> lookupSEnv (symbol name) $ to_core_expr_sort s)

insertLocalId :: Symbolic a => a -> Id -> ToCore ()
insertLocalId name idx = modify (\s -> s {to_core_ids = insertSEnv (symbol name) idx (to_core_ids s)})

lookupLocalId :: Symbolic a => a -> ToCore (Maybe Id)
lookupLocalId name = gets (\s -> lookupSEnv (symbol name) $ to_core_ids s)

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
runToCoreDef cgi tc = flip evalStateT defaultToCoreState . flip runReaderT info . unToCoreM
  where
    info = (defaultToCoreInfo cgi) { to_core_tycons = tc }

runToCore :: HscEnv -> RuleBase -> UniqSupply -> Module -> ModuleSet -> PrintUnqualified -> SrcSpan -> CGInfo -> TCEmb TyCon -> ToCore a -> IO (a, SimplCount)
runToCore he rb us mod ms pu ss cgi tc = runCoreM he rb us mod ms pu ss . runToCoreDef cgi tc
