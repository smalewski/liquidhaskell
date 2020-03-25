{-# OPTIONS_GHC -Wwarn #-}
{-# LANGUAGE DeriveFunctor        #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Gradual.CastInsertion.Casting (
  castInsertion,
  castInsertions,
  castCore
  ) where

import           Debug.Trace
import           CoreSyn
import           CoreUtils
import qualified Data.HashMap.Strict                      as M
import           Data.List                                (any)
import           Data.Maybe                               (fromMaybe, mapMaybe, maybeToList)
import           FastString
import           Id
import           MkCore
import           Module                                   (moduleName, emptyModuleSet)
import           Name
import           SrcLoc                                   (noSrcSpan)
import           Type                                     hiding (isFunTy)
import           TysWiredIn
import           UniqSupply
import           Unique
import           HscTypes
import           Outputable (alwaysQualify)
import           Rules (emptyRuleBase)

import           Gradual.CastInsertion.ExprToCore
import           Gradual.CastInsertion.Monad
import           Language.Fixpoint.Types                  (HasGradual (..),
                                                           Symbol, Symbolic)
import qualified Language.Fixpoint.Types                  as F
import           Language.Fixpoint.Types.PrettyPrint      (Tidy (..))
import           Language.Haskell.Liquid.Constraint.Types
import           Language.Haskell.Liquid.Misc
import           Language.Haskell.Liquid.Types            hiding (binds)
import           Language.Haskell.Liquid.Types.RefType (toType)
import           Language.Haskell.Liquid.UX.Tidy          (tidySpecType)
import           Language.Haskell.Liquid.GHC.Misc                      (showCBs)
import           Language.Haskell.Liquid.Types.Literals (literalSpecType)
import           Language.Haskell.Liquid.Transforms.CoreToLogic (logicType)

-- TEMPORARY ORPHAN INSTANCES
-- Forgive me god

-- instance (Functor f, Foldable f, HasGradual a) => HasGradual (f a) where
--   isGradual x = Data.List.any $ isGradual <$> x
--   gVars = undefined
--   ungrad = fmap ungrad

instance HasGradual a => HasGradual (Maybe a) where
  isGradual Nothing  = False
  isGradual (Just x) = isGradual x

  gVars Nothing  = []
  gVars (Just x) = gVars x

  ungrad = fmap ungrad


dom' :: SpecType -> Maybe SpecType
dom' (RFun _ i _ _) = Just i
dom' (RAllT _ s) = dom' s
dom' (RAllP _ s) = dom' s
dom' (RAllS _ s) = dom' s
dom' (RAllE _ _ s) = dom' s
dom' (RAppTy arg _ _) = Just arg
dom' s@(RVar x r) = Just s
dom' _              = Nothing

cod' :: SpecType -> Maybe SpecType
cod' (RFun _ _ o _) = Just o
cod' (RAllT _ s) = Just s
cod' (RAllP _ s) = cod' s
cod' (RAllS _ s) = cod' s
cod' (RAllE _ _ s) = cod' s
cod' (RAppTy _ res _) = Just res
cod' s@(RVar x r) = Just s
cod' (RHole _) = Nothing
cod' _         = Nothing

dom :: SpecType -> ToCore SpecType
dom = liftMaybe "dom is not defined for non function types." . dom'

cod :: SpecType -> ToCore SpecType
cod = liftMaybe "cod is not defined for non function types." . cod'

insertCast :: SpecType -> SpecType -> CoreExpr -> ToCore CoreExpr
insertCast myr tgr expr
  | isFunTy myr = expandCast myr tgr expr
  | otherwise   = if isTrivial utgr && not (isGradual myr) then pure expr else castedExpr
  -- = do ok <- checkSub myr tgr   -- myr <: tgr
  --      if ok
  --        then pure expr
  --        else castedExpr
  where
    utgr = ungrad tgr
    reft = rTypeReft utgr
    checkExpr v = mkIfThenElse <$> specToCore tgr v <*> pure (Var v) <*> pure errExpr
    castedExpr = do
      v <- freshId "v" ty
      bindNonRec v expr <$> checkExpr v
    errExpr = mkRuntimeErrorApp rUNTIME_ERROR_ID ty errMsg
    errMsg = "Cast error: " ++ show reft ++ " is not satisfied."
    ty = exprType expr

expandCast :: SpecType -> SpecType -> CoreExpr -> ToCore CoreExpr
expandCast myr tgr e = do
  ty <- toType <$> dom myr
  x <- freshId "x" ty
  y <- freshId "y" ty
  let fs = (,y) <$> mapMaybe mySymbol [myr, tgr]
  let ey = mkCoreApps e [Var y]
  xCast <- insertCast <$> dom tgr <*> dom myr <*> pure (Var x)
  eyCast <- withSubs fs [] $ insertCast <$> cod myr <*> cod tgr <*> pure ey
  body <- bindNonRec y <$> xCast <*> eyCast
  pure $ mkCoreLams [x] body

mySymbol :: SpecType -> Maybe Symbol
mySymbol (RVar x _) = Just $ F.symbol x
mySymbol (RFun x _ _ _) = Just x
mySymbol (RAllP pv _) = Just (pname pv)
mySymbol (RAllT rtv _) =
  let b = fst <$> rTVarToBind rtv
  in Just $ fromMaybe (F.symbol ("_" :: String)) b
mySymbol (RAllS s _) = Just s
mySymbol (RAllE s _ _) = Just s
mySymbol (REx _ _ t) = mySymbol t
mySymbol (RAppTy _ _ p) = Just . F.reftBind . ur_reft $ p
mySymbol (RApp _ _ _ r) = Just . F.reftBind . ur_reft $ r
mySymbol _          = Nothing

exprSType :: CoreExpr -> ToCore SpecType
exprSType (Var x) = lookupSType x
exprSType (App f _) = exprSType f >>= cod
exprSType (Let _ e) = exprSType e
exprSType (Tick _ e) = exprSType e
exprSType (Cast e _) = exprSType e
exprSType (Lam x e) =
    rFun (F.symbol x) <$> lookupSType x <*> exprSType e
exprSType (Lit l) = pure $ literalSpecType l
exprSType (Case e b t alts) = altSType (head alts)
exprSType (Type t) = pure $ logicType t
exprSType _ = fail "Expression doesn't have type."

altSType :: CoreAlt -> ToCore SpecType
altSType (_, _, e) = exprSType e

fstMaybe :: Maybe a -> Maybe a -> Maybe a
fstMaybe Nothing y = y
fstMaybe x _       = x

castInsertions :: [CoreBind] -> ToCore [CoreBind]
castInsertions bs = mapM castInsertionBind bs

castInsertion :: CoreBind -> ToCore CoreBind
castInsertion b@(NonRec x _) = withTopVar x $ castInsertionBind b
castInsertion (Rec bs) = Rec <$> mapM (\xe@(x,_) -> withTopVar x $ castInRec xe) bs


castInsertionBind :: CoreBind -> ToCore CoreBind
castInsertionBind (NonRec x expr) = do
  spec       <- lookupSType x
  (expr', _) <- castInsertionExpr (Just spec) expr
  pure $ NonRec x expr'
castInsertionBind (Rec bs) = Rec <$> mapM castInRec bs

castInRec :: (CoreBndr, CoreExpr) -> ToCore (CoreBndr, CoreExpr)
castInRec ir@(bnd, expr) = do
  spec <- lookupSType bnd
  (expr', _) <- castInsertionExpr (Just spec) expr
  pure (bnd, expr')

isClassDict :: CoreExpr -> Bool
isClassDict (Var x) = take 2 (getOccString x) == "$f"
isClassDict _       = False

castInsertionExpr :: Maybe SpecType -> CoreExpr -> ToCore (CoreExpr, Maybe SpecType)
castInsertionExpr myr expr = case expr of
  Var x -> (expr,) <$> (Just <$> lookupSType x)
  -- Lit l -> pure (expr, Just $ literalSpecType l)
  Lit l -> pure (expr, myr)
  App fun arg -> do
    funReft   <- exprSType fun
    argReft   <- exprSType arg
    (arg', argSpec) <- castInsertionExpr (Just argReft) arg
    funDomSym <- liftMaybe "not fun" $ mySymbol funReft
    let fs = [(funDomSym, arg)]
    (fun', funSpec) <- withSubs [] fs $ castInsertionExpr (Just funReft) fun
    let parg = pure arg'
    let castedArg = fromMaybe parg $ do
          fromS <- argSpec
          toS   <- funSpec >>= dom'
          Just $ parg >>= insertCast fromS toS
    arg'' <- castedArg
    pure (App fun' arg'', funSpec >>= cod')
  Lam x body -> do
    let fs = fmap (,x) $ mapMaybe mySymbol $ maybeToList myr
    (body', bodySpec) <- castInsertionExpr (myr >>= cod') body
    body'' <- withSubs fs [] $ pure body'
    spec   <- traverse (funSpecT x) bodySpec
    pure (Lam x body'', spec)
  Let b e -> do
    b'          <- castInsertionBind b
    (e', eSpec) <- castInsertionExpr myr e
    pure (Let b' e', eSpec)
  Case e x t alts -> do
    (e', eSpec)       <- castInsertionExpr Nothing e
    (alts', joinSpec) <- castInsertionAlts alts
    pure (Case e' x t alts', joinSpec)
  Cast e coer -> do
    (e', eSpec) <- castInsertionExpr myr e
    pure (Cast e' coer, eSpec)
  Tick tick e -> do
    (e', eSpec) <- castInsertionExpr myr e
    pure (Tick tick e', eSpec)
  Type{} -> pure (expr, Nothing)
  Coercion{} -> pure (expr, Nothing)

funSpecT :: Var -> SpecType -> ToCore SpecType
funSpecT x et = rFun (F.symbol x) <$> lookupSType x <*> pure et

instance Show CoreBind where
  show (NonRec x _) = "NonRec " ++ show x
  show (Rec xs) = "Rec " ++ show (fmap fst xs)

castInsertionAlts :: [CoreAlt] -> ToCore ([CoreAlt], Maybe SpecType)
castInsertionAlts alts = do
  let altExpr (_, _, e) = e
  specs <- mapM (exprSType . altExpr) alts
  joinSpec <- join specs
  alts' <- mapM (castInsertionAlt joinSpec) alts
  pure (alts', joinSpec)

castInsertionAlt :: Maybe SpecType -> CoreAlt -> ToCore CoreAlt
castInsertionAlt tgr (con, xs, e) = do
    (e', eSpec)  <- castInsertionExpr Nothing e
    let needed = any F.isGradual [eSpec, tgr]
    e'' <- ifButNothing needed (insertCast <$> eSpec <*> tgr <*> pure e') $ pure e'
    pure (con, xs, e'')

join :: [SpecType] -> ToCore (Maybe SpecType)
join specs = pure $ headMaybe specs

ifButNothing :: Bool -> Maybe a -> a -> a
ifButNothing _ Nothing y     = y
ifButNothing False _ y       = y
ifButNothing True (Just x) _ = x

headMaybe :: [a] -> Maybe a
headMaybe [] = Nothing
headMaybe (x:_) = Just x

castCore :: CGInfo -> ModGuts -> IO (CGInfo, ModGuts)
castCore cgi modGuts= do
  let gi = ghcI cgi
  let hscEnv = env gi
  let rules = emptyRuleBase
  uniq <- mkSplitUniqSupply 'c'
  let printUnq = alwaysQualify
  let mod     = mg_module modGuts
  let modSet = emptyModuleSet
  let srcSpan = mg_loc modGuts
  let cbs     = mg_binds modGuts

  let tcemb = gsTcEmbeds $ spec gi

  let castedCore = castInsertions cbs
  (newCore, _) <- runToCore hscEnv rules uniq mod modSet printUnq srcSpan cgi tcemb castedCore
  -- putStrLn "AFTER"
  putStrLn $ showCBs False newCore
  let cgi' = cgi {ghcI = gi {cbs = newCore}}
  let modGuts' = modGuts {mg_binds = newCore}

  return (cgi', modGuts')
