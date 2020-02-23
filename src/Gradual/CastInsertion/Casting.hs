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
  castInsertions
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
import           Module                                   (moduleName)
import           Name
import           SrcLoc                                   (noSrcSpan)
import           Type                                     hiding (isFunTy)
import           TysWiredIn
import           UniqSupply
import           Unique

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

instance Eq a => Eq (UReft a) where
  r1 == r2 = (ur_reft r1) == (ur_reft r2)

instance HasGradual a => HasGradual (Located a) where
  isGradual = isGradual . val
  gVars = gVars . val
  ungrad l = l { val = ungrad (val l) }

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
dom' _              = Nothing

cod' :: SpecType -> Maybe SpecType
cod' (RFun _ _ o _) = Just o
cod' (RAllT _ s) = cod' s
cod' (RAllP _ s) = cod' s
cod' (RAllS _ s) = cod' s
cod' (RAllE _ _ s) = cod' s
cod' _              = Nothing

dom :: SpecType -> ToCore SpecType
dom = liftMaybe "dom is not defined for non function types." . dom'

cod :: SpecType -> ToCore SpecType
cod = liftMaybe "cod is not defined for non function types." . cod'

-- Needs to replace with proper subtyping checking.
compareSpecTypes :: SpecType -> SpecType -> Bool
compareSpecTypes (RVar _ r1) (RVar _ r2) = r1 == r2
compareSpecTypes (RFun _ i1 o1 r1) (RFun _ i2 o2 r2) = compareSpecTypes i1 i2 && compareSpecTypes o1 o2 && r1 == r2
compareSpecTypes (RAllT _ s1) (RAllT _ s2) = compareSpecTypes s1 s2
compareSpecTypes (RAllP _ s1) (RAllP _ s2) = compareSpecTypes s1 s2
compareSpecTypes (RAllS _ s1) (RAllS _ s2) = compareSpecTypes s1 s2
compareSpecTypes (RApp _ args1 _ r1) (RApp _ args2 _ r2) = r1 == r2 && and (zipWith compareSpecTypes args1 args2)
compareSpecTypes (RAllE _ a1 s1) (RAllE _ a2 s2) = compareSpecTypes a1 a2 && compareSpecTypes s1 s2
compareSpecTypes (REx _ a1 t1) (REx _ a2 t2) = compareSpecTypes a1 a2 && compareSpecTypes t1 t2
compareSpecTypes (RExprArg l1) (RExprArg l2) = l1 == l2
compareSpecTypes (RAppTy a1 re1 r1) (RAppTy a2 re2 r2) = r1 == r2 && compareSpecTypes a1 a2 && compareSpecTypes re1 re2
compareSpecTypes (RRTy _ r1 _ t1) (RRTy _ r2 _ t2) = r1 == r2 && compareSpecTypes t1 t2
compareSpecTypes (RHole r1) (RHole r2) = r1 == r2
compareSpecTypes _ _ = False


holds :: SpecType -> SpecType -> Bool
holds p q = isTrivial q || compareSpecTypes (ungrad p) (ungrad q)

insertCast :: SpecType -> SpecType -> CoreExpr -> ToCore CoreExpr
insertCast myr tgr expr
  | holds myr tgr = pure expr
  | isFunTy myr   = expandCast myr tgr expr
  | otherwise     = castedExpr
  where
    reft = ungrad $ rTypeReft tgr
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
  eyCast <- withSubs fs $ insertCast <$> cod myr <*> cod tgr <*> pure ey
  body <- bindNonRec y <$> xCast <*> eyCast
  pure $ mkCoreLams [x] body

mySymbol :: SpecType -> Maybe Symbol
mySymbol (RFun x _ _ _) = Just x
mySymbol (RAllT _ t) = mySymbol t
mySymbol (RAllP _ t) = mySymbol t
mySymbol (RAllS _ t) = mySymbol t
mySymbol (RAllE _ _ t) = mySymbol t
mySymbol (REx _ _ t) = mySymbol t
mySymbol _ = Nothing

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
castInsertion = castInsertionBind

castInsertionBind :: CoreBind -> ToCore CoreBind
castInsertionBind (NonRec x expr) = do
  spec       <- lookupSType x
  (expr', _) <- castInsertionExpr (Just spec) expr
  pure $ NonRec x expr'
castInsertionBind (Rec bs) = Rec <$> mapM castInRec bs
  where
    castInRec :: (CoreBndr, CoreExpr) -> ToCore (CoreBndr, CoreExpr)
    castInRec ir@(bnd, expr) = do
      spec <- lookupSType bnd
      (expr', _) <- castInsertionExpr (Just spec) expr
      pure (bnd, expr')

castInsertionExpr :: Maybe SpecType -> CoreExpr -> ToCore (CoreExpr, Maybe SpecType)
castInsertionExpr myr expr = case expr of
  Var x -> (expr,) <$> (Just <$> lookupSType x)
  -- Lit l -> pure (expr, Just $ literalSpecType l)
  Lit l -> pure (expr, myr)
  App fun arg -> do
    funReft   <- exprSType fun
    argReft   <- exprSType arg
    (fun', funSpec) <- castInsertionExpr (Just funReft) fun
    (arg', argSpec) <- castInsertionExpr (Just argReft) arg
    let parg = pure arg'
    let castedArg = fromMaybe parg $ do
          fromS <- argSpec
          toS   <- funSpec >>= dom'
          Just $ parg >>= insertCast fromS toS
    arg'' <- if isGradual argReft then castedArg else parg
    pure (App fun' arg'', funSpec >>= cod')
  Lam x body -> do
    let fs = fmap (,x) $ mapMaybe mySymbol $ maybeToList myr
    (body', bodySpec) <- castInsertionExpr (myr >>= cod') body
    body'' <- withSubs fs $ pure body'
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

-- Helpers

infixl 4 *>>
(*>>) :: Applicative f => f (a -> b) -> a -> f b
f *>> x = f <*> pure x

ifButNothing :: Bool -> Maybe a -> a -> a
ifButNothing _ Nothing y     = y
ifButNothing False _ y       = y
ifButNothing True (Just x) _ = x

headMaybe :: [a] -> Maybe a
headMaybe [] = Nothing
headMaybe (x:_) = Just x
