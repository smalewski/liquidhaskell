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
  ftyconTycon
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

import           Language.Fixpoint.Types       (SEnv, Symbolic (..), emptySEnv, Sort,
                                                insertSEnv, lookupSEnv, Symbol, TCEmb, FTycon)
import           Language.Haskell.Liquid.Types ()

newtype ToCore a = ToCore {
  unToCoreM :: ReaderT ToCoreInfo (StateT ToCoreState CoreM) a
  } deriving (Functor, Applicative, Monad, MonadState ToCoreState, MonadReader ToCoreInfo, MonadIO)

data ToCoreState = ToCoreState {
  to_core_ids :: SEnv Id,
  to_core_expr_sort :: SEnv Sort
  } deriving (Show)

data ToCoreInfo = ToCoreInfo {
  to_core_ftycons :: M.HashMap FTycon TyCon,
  to_core_tycons :: M.HashMap TyCon FTycon
  } deriving (Show)

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

emptyToCoreState :: ToCoreState
emptyToCoreState = ToCoreState {to_core_ids = mempty, to_core_expr_sort = mempty}

emptyToCoreInfo :: ToCoreInfo
emptyToCoreInfo = ToCoreInfo {to_core_ftycons = mempty, to_core_tycons = mempty}

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

freshId :: Type -> ToCore Id
freshId ty = do
  uniq <- getUniqueM
  let occ = mkVarOcc "c"
  let name = mkInternalName uniq occ noSrcSpan
  pure $ mkLocalId name ty

runToCoreDef :: TCEmb TyCon -> ToCore a -> CoreM a
runToCoreDef tc = flip evalStateT emptyToCoreState . flip runReaderT info . unToCoreM
  where
    info = emptyToCoreInfo { to_core_tycons = tc }

runToCore :: HscEnv -> RuleBase -> UniqSupply -> Module -> ModuleSet -> PrintUnqualified -> SrcSpan -> TCEmb TyCon -> ToCore a -> IO (a, SimplCount)
runToCore he rb us mod ms pu ss tc = runCoreM he rb us mod ms pu ss . runToCoreDef tc
