{-# OPTIONS_GHC -Wwarn #-}
{-# LANGUAGE DeriveFunctor        #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Gradual.CastInsertion.Casting (
  castInsertion,
  castInsertions,
  getSpecs,
  ) where

import           Debug.Trace
import           CoreSyn
import           CoreUtils
import qualified Data.HashMap.Strict                      as M
import           Data.List                                (any)
import           Data.Maybe                               (fromMaybe)
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

type Refinements = F.SEnv SpecType

getSpecs :: CGInfo -> [(Symbol, SpecType)]
getSpecs cg = concat $ localSpecs ++ globalSpecs
  where
    localSpecs = cgToSpecs reLocal
    globalSpecs = cgToSpecs reGlobal
    toMaps f = fmap (f . renv . senv) . hsCs
    cgToSpecs f = M.toList <$> toMaps f cg

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


dom :: SpecType -> Maybe SpecType
dom (RFun _ i _ _) = Just i
dom (RAllT _ s) = dom s
dom (RAllP _ s) = dom s
dom (RAllS _ s) = dom s
dom (RAllE _ _ s) = dom s
dom _              = Nothing

cod :: SpecType -> Maybe SpecType
cod (RFun _ _ o _) = Just o
cod (RAllT _ s) = cod s
cod (RAllP _ s) = cod s
cod (RAllS _ s) = cod s
cod (RAllE _ _ s) = cod s
cod _              = Nothing

lookupSType :: Symbolic a => Refinements -> a -> Maybe SpecType
lookupSType refts x = F.lookupSEnv (F.symbol x) refts


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
    castedExpr = mkIfThenElse <$> check <*> pure expr <*> pure errExpr
    errExpr = mkRuntimeErrorApp rUNTIME_ERROR_ID ty errMsg
    errMsg = "Cast error: " ++ show reft ++ " is not satisfied."
    ty = exprType expr
    check = specToCore tgr

dom' :: SpecType -> SpecType
dom' s = fromMaybe (error "DOm") (dom s) -- FIXME

cod' :: SpecType -> SpecType
cod' s = fromMaybe (error "COD") (cod s) -- FIXME

expandCast :: SpecType -> SpecType -> CoreExpr -> ToCore CoreExpr
expandCast myr tgr e = do
  let ty = toType $ dom' myr
  x <- freshId ty
  y <- freshId ty
  let ey = trace ("IDs :" ++ show x ++ ", " ++ show y) mkCoreApps e [Var y]
  xCast <- insertCast (dom' tgr) (dom' myr) (Var x)
  eyCast <- insertCast (cod' myr) (cod' tgr) ey -- FIXME Need tysubst
  pure $ bindNonRec y xCast eyCast

exprSType :: Refinements -> Maybe SpecType -> CoreExpr -> Maybe SpecType
exprSType refts myr (Var x) = fstMaybe (lookupSType refts x) myr
exprSType refts myr (App f _) = exprSType refts (myr >>= dom) f >>= cod
exprSType refts myr (Let _ e) = exprSType refts myr e
exprSType refts myr (Tick _ e) = exprSType refts myr e
exprSType refts myr (Cast e _) = exprSType refts myr e
exprSType refts myr (Lam x e) = rFun (F.symbol x) <$> xReft <*> eReft
  where
    xReft = fstMaybe (lookupSType refts x) $ myr >>= dom
    eReft = fstMaybe (exprSType refts (myr >>= cod) e) myr
exprSType _ myr _ = myr

fstMaybe :: Maybe a -> Maybe a -> Maybe a
fstMaybe Nothing y = y
fstMaybe x _       = x

castInsertions :: Refinements -> [CoreBind] -> ToCore [CoreBind]
castInsertions refts bs = mapM (castInsertionBind refts) bs

castInsertion :: Refinements -> CoreBind -> ToCore CoreBind
castInsertion = castInsertionBind

castInsertionBind :: Refinements -> CoreBind -> ToCore CoreBind
castInsertionBind refts (NonRec x expr) =
  NonRec x <$> castInsertionExpr refts (lookupSType refts x) expr
castInsertionBind refts (Rec bs) = Rec <$> mapM castInRec bs
  where
    castInRec :: (CoreBndr, CoreExpr) -> ToCore (CoreBndr, CoreExpr)
    castInRec ir@(bnd, _) = mapM (castInsertionExpr refts (lookupSType refts bnd)) ir

castInsertionExpr :: Refinements -> Maybe SpecType -> CoreExpr -> ToCore CoreExpr
castInsertionExpr refts myr expr = case expr of
  Var{} -> pure expr
  Lit{} -> pure expr
  App fun arg -> App <$> fun' <*> arg''
    where
      arg''     = if isGradual argReft then castedArg else arg'
      funReft   = exprSType refts Nothing fun
      argReft   = exprSType refts Nothing arg
      fun'      = castInsertionExpr refts funReft fun
      arg'      = castInsertionExpr refts argReft arg
      castedArg = fromMaybe arg' $ do
        fromR <- argReft
        toR   <- funReft >>= dom
        pure $ arg' >>= insertCast fromR toR
  Lam x body -> Lam x <$> body'
    where
      body' = castInsertionExpr refts (myr >>= cod) body
  Let b e -> Let <$> b' <*> e'
    where
      b' = castInsertionBind refts b
      e' = castInsertionExpr refts myr e
  Case e x t alts -> Case <$> e' *>> x *>> t <*> alts'
    where
      eReft = exprSType refts Nothing e
      e'    = castInsertionExpr refts eReft e
      alts' = mapM (castInsertionAlt refts myr) alts
  Cast e coer -> Cast <$> castInsertionExpr refts myr e *>> coer
  Tick tick e -> Tick tick <$> castInsertionExpr refts myr e
  Type{} -> pure expr
  Coercion{} -> pure expr

castInsertionAlt :: Refinements -> Maybe SpecType -> CoreAlt -> ToCore CoreAlt
castInsertionAlt refts tgr (con, xs, e) = do
    let myr = exprSType refts tgr e
    e'  <- castInsertionExpr refts myr e
    let needed = any F.isGradual [myr, tgr]
    e'' <- ifButNothing needed (insertCast <$> myr <*> tgr *>> e') $ pure e'
    pure (con, xs, e'')



-- Helpers

infixl 4 *>>
(*>>) :: Applicative f => f (a -> b) -> a -> f b
f *>> x = f <*> pure x

ifButNothing :: Bool -> Maybe a -> a -> a
ifButNothing _ Nothing y     = y
ifButNothing False _ y       = y
ifButNothing True (Just x) _ = x

