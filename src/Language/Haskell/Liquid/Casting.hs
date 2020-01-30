{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

module Language.Haskell.Liquid.Casting (
  castInsertion, getSpecs
  ) where

import           Data.List (any)
import           CoreSyn
import           CoreUtils
import           Data.Maybe (fromMaybe)
import           Unique
import           Id
import           Name
import           FastString
import qualified Data.HashMap.Strict as M
import qualified Language.Fixpoint.Types as F
import           Language.Fixpoint.Types (Symbolic, Symbol, HasGradual (..))
import           Language.Haskell.Liquid.Types hiding (binds)
import           Language.Haskell.Liquid.Constraint.Types

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

  gVars (RVar _ r) = gVars r
  gVars (RFun _ r i o) =  gVars r ++ gVars i ++ gVars o
  gVars (RAllT _ b) = gVars b
  gVars (RAllP _ b) = gVars b
  gVars (RAllS _ b) = gVars b
  gVars (RApp _ args _ r) = concat (gVars <$> args) ++ gVars r
  gVars (RAllE _ args ty) = gVars args ++ gVars ty
  gVars (REx _ args ty) = gVars args ++ gVars ty
  gVars (RExprArg lexpr) = gVars lexpr
  gVars (RAppTy arg res r) = concat (gVars <$> [arg, res]) ++ gVars r
  gVars (RRTy env ref _ ty) = (env >>= gVars . snd) ++ gVars ref ++ gVars ty
  gVars (RHole r) = gVars r

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
  isGradual Nothing = False
  isGradual (Just x) = isGradual x

  gVars Nothing = []
  gVars (Just x) = gVars x

  ungrad = fmap ungrad


dom :: SpecType -> Maybe SpecType
dom (RFun _ i _ _) = Just i
dom _              = Nothing

cod :: SpecType -> Maybe SpecType
cod (RFun _ _ o _) = Just o
cod _              = Nothing

lookupSType :: Symbolic a => Refinements -> a -> Maybe SpecType
lookupSType refts x = F.lookupSEnv (F.symbol x) refts


-- Needs to replace with proper subtyping checking.
compareSpecTypes :: SpecType -> SpecType -> Bool
compareSpecTypes (RVar _ r1) (RVar _ r2) = r1 == r2
compareSpecTypes (RFun _ i1 o1 r1) (RFun _ i2 o2 r2) = compareSpecTypes i1 i2 && compareSpecTypes o1 o2 && r1 == r2
compareSpecTypes _ _ = False


holds :: SpecType -> SpecType -> Bool
holds p q = compareSpecTypes (ungrad p) (ungrad q)

insertCast :: SpecType -> SpecType -> CoreExpr -> CoreExpr
insertCast myr tgr expr
  | holds myr tgr = expr
  | otherwise     = castedExpr
  where
    castedExpr = bindNonRec (mkLocalId name ty) strLit expr
    strLit = mkStringLit $ "Casting: " ++ show myr ++ " => " ++ show tgr
    ty = exprType strLit
    name = mkSystemName (mkVarOccUnique $ fsLit varName) (mkVarOcc varName)
    varName = "casting"

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
fstMaybe Nothing y  = y
fstMaybe x _        = x

castInsertion :: Refinements -> [CoreBind] -> [CoreBind]
castInsertion refts bs = castInsertionBind refts <$> bs

castInsertionBind :: Refinements -> CoreBind -> CoreBind
castInsertionBind refts (NonRec x expr) =
  NonRec x $ castInsertionExpr refts (lookupSType refts x) expr
castInsertionBind refts (Rec bs) = Rec $ castInRec <$> bs
  where
    castInRec (bnd, expr) =
      (bnd, castInsertionExpr refts (lookupSType refts bnd) expr)

castInsertionExpr :: Refinements -> Maybe SpecType -> CoreExpr -> CoreExpr
castInsertionExpr refts myr expr = case expr of
  Var{} -> expr
  Lit{} -> expr
  App fun arg
    | isGradual argReft   -> App fun' castedArg
    | otherwise           -> App fun' arg'
    where
      funReft =  exprSType refts Nothing fun
      argReft =  exprSType refts Nothing arg
      fun' = castInsertionExpr refts funReft fun
      arg' = castInsertionExpr refts argReft arg
      castedArg = fromMaybe arg' $ do
        fromR <- argReft
        toR <- funReft >>= dom
        return $ insertCast fromR toR arg'
  Lam x body -> Lam x body'
    where
      body' = castInsertionExpr refts (myr >>= cod) body
  Let b e -> Let b' e'
    where
      b' = castInsertionBind refts b
      e' = castInsertionExpr refts myr e
  Case e x t alts -> Case e' x t alts'
    where
      eReft = exprSType refts Nothing e
      e' = castInsertionExpr refts eReft e
      alts' = castInsertionAlt refts myr <$> alts
  Cast e coer -> Cast (castInsertionExpr refts myr e) coer
  Tick tick e -> Tick tick $ castInsertionExpr refts myr e
  Type{} -> expr
  Coercion{} -> expr

castInsertionAlt :: Refinements -> Maybe SpecType -> CoreAlt -> CoreAlt
castInsertionAlt refts tgr (con, xs, e) = (con, xs, e'')
  where
    myr = exprSType refts tgr e'
    e' = castInsertionExpr refts myr e
    e'' = if any F.isGradual [myr, tgr] then
      fromMaybe e' $ do myr' <- myr
                        tgr' <- tgr
                        return $ insertCast myr' tgr' e'
          else e'

-- Constructing the casts

-- reftToCoreExpr :: Reft -> CoreExpr
-- reftToCoreExpr = undefined
