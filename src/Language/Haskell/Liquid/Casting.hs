{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveFunctor #-}

module Language.Haskell.Liquid.Casting (
  castInsertion, mkRefinements, toRefMap, getSpecs
  ) where

import           CoreSyn
import           CoreUtils
-- import           Data.Bifunctor
-- import           Data.List (sortOn)
import           Data.Maybe (fromMaybe)
-- import           MkCore
import           Unique
import           Id
import           Name
-- import           Type
-- import           Type
-- import           OccName
import           FastString
-- import           Literal (Literal)
import qualified Data.HashMap.Strict as M
import qualified Language.Fixpoint.Types as F
import           Language.Fixpoint.Types (Symbolic, Reft (..), Symbol, HasGradual (..))
import           Language.Haskell.Liquid.Types hiding (binds)
import           Language.Haskell.Liquid.Constraint.Types
-- import           Language.Haskell.Liquid.GHC.Misc (showCBs)
-- import           System.IO.Unsafe (unsafePerformIO)
-- import           Control.DeepSeq (deepseq)

data SRef a b = DFun a b (SRef a b) (SRef a b)
              | DTFun (Maybe a) (SRef a b) -- Should we preserve the kind?
              | Ref (Maybe a) b
              | Noref
              deriving (Eq, Show, Functor)

type SReft = SRef Symbol Reft

instance HasGradual b => HasGradual (SRef a b) where
  isGradual (DFun _ r i o) = isGradual r || isGradual i || isGradual o
  isGradual (DTFun _ b) = isGradual b
  isGradual (Ref _ r) = isGradual r
  isGradual Noref = False

  gVars (DFun _ r i o) = gVars r ++ gVars i ++ gVars o
  gVars (DTFun _ b) = gVars b
  gVars (Ref _ r) = gVars r
  gVars Noref = []

  ungrad = fmap ungrad

type Refinements = M.HashMap Symbol SReft

mkRefinements :: CGInfo -> Refinements
mkRefinements cg = bnds cg
  where
    bnds = M.fromList . (fmap . fmap) (Ref Nothing . F.sr_reft) . M.elems . F.beBinds . binds

-- Doesn't collect refinements of type constructor's arguments.
-- (e.g would not get the Pos in [Pos]])
specToSRReft :: SpecType -> SRef Symbol RReft
specToSRReft (RVar x r) = Ref (Just $ F.symbol x) r
specToSRReft (RFun x i o r) = DFun x r (specToSRReft i) (specToSRReft o)
specToSRReft (RAllT v t) = DTFun (fst <$> rTVarToBind v) (specToSRReft t) -- Droping kind :S
specToSRReft (RApp _ _ _ r) = Ref Nothing r  -- fix
specToSRReft (RAppTy _ _ r) = Ref Nothing r
specToSRReft _ = Noref

specToSReft :: SpecType -> SReft
specToSReft s = ur_reft <$> specToSRReft s

toRefMap :: [(Symbol, SpecType)] -> Refinements
toRefMap = M.fromList . (fmap . fmap) specToSReft

-- printReftMap :: [Refinements] -> IO ()
-- printReftMap = mapM_ (mapM_ print . M.toList)

getSpecs :: CGInfo -> [(Symbol, SpecType)]
getSpecs cg = concat $ localSpecs ++ globalSpecs
  where
    localSpecs = cgToSpecs reLocal
    globalSpecs = cgToSpecs reGlobal
    toMaps f = fmap (f . renv . senv) . hsCs
    cgToSpecs f = M.toList <$> toMaps f cg

-- insertReft :: Symbolic a => a -> SReft -> Refinements -> Refinements
-- insertReft = M.insert . F.symbol

dom :: SReft -> SReft
dom (DFun _ _ i _) = i
dom _ = Noref

cod :: SReft -> SReft
cod (DFun _ _ _ o) = o
cod _ = Noref

lookupSReft :: Symbolic a => Refinements -> a -> Maybe SReft
lookupSReft refts x = M.lookup (F.symbol x) refts

lookupSReftDef :: Symbolic a => Refinements -> a -> SReft
lookupSReftDef refts = fromMaybe Noref . lookupSReft refts

-- maybeToRefts :: Maybe (Symbol, SReft) -> Refinements
-- maybeToRefts = M.fromList . maybeToList

holds :: SReft -> SReft -> Bool
holds p q = (F.ungrad p) == (F.ungrad q)

insertCast :: SReft -> SReft -> CoreExpr -> CoreExpr
insertCast myr tgr expr
  | holds myr tgr = expr
  | otherwise     = castedExpr
  where
    castedExpr = bindNonRec (mkLocalId name ty) strLit expr
    strLit = mkStringLit $ "Casting: " ++ show myr ++ " => " ++ show tgr
    ty = exprType strLit
    name = mkSystemName (mkVarOccUnique $ fsLit varName) (mkVarOcc varName)
    varName = "casting"

ifNoref :: SReft -> SReft -> SReft
ifNoref x Noref = x
ifNoref _ y     = y

exprReft :: Refinements -> SReft -> CoreExpr -> SReft
exprReft refts myr (Var x) = fromMaybe myr $ lookupSReft refts x
exprReft refts myr (App f _) = cod $ exprReft refts (dom myr) f
exprReft refts myr (Let _ e) = exprReft refts myr e
exprReft refts myr (Tick _ e) = exprReft refts myr e
exprReft refts myr (Cast e _) = exprReft refts myr e
exprReft refts myr (Lam x e) = DFun (F.symbol x) F.trueReft xReft eReft
  where
    xReft = fromMaybe (dom myr) $ lookupSReft refts x
    eReft = ifNoref myr $ exprReft refts (cod myr) e
exprReft _ myr _ = myr

castInsertion :: Refinements -> [CoreBind] -> [CoreBind]
castInsertion refts bs = castInsertionBind refts <$> bs

castInsertionExpr :: Refinements -> SReft -> CoreExpr -> CoreExpr
castInsertionBind :: Refinements -> CoreBind -> CoreBind
castInsertionBind refts (NonRec x expr) =
  NonRec x $ castInsertionExpr refts (lookupSReftDef refts x) expr
castInsertionBind refts (Rec bs) =
  Rec $ castInRec <$> bs
  where
    castInRec (bnd, expr) = (bnd, castInsertionExpr refts (lookupSReftDef refts bnd) expr)

castInsertionExpr refts myr expr = case expr of
  Var{} -> expr
  Lit{} -> expr
  App fun arg
    | F.isGradual argReft -> App fun' castedArg
    | otherwise           -> App fun' arg'
    where
      funReft =  exprReft refts Noref fun
      argReft =  exprReft refts Noref arg
      arg' = castInsertionExpr refts argReft arg
      fun' = castInsertionExpr refts funReft fun
      castedArg = insertCast argReft (dom funReft) arg'
  Lam x body -> Lam x body'
    where
      body' = castInsertionExpr refts (cod myr) body
  Let b e -> Let b' e'
    where
      b' = castInsertionBind refts b
      e' = castInsertionExpr refts myr e
  Case e x t alts -> Case e' x t alts'
    where
      eReft = exprReft refts Noref e
      e' = castInsertionExpr refts eReft e
      alts' = castInsertionAlt refts myr <$> alts
  Cast e coer -> Cast (castInsertionExpr refts myr e) coer
  Tick tick e -> Tick tick $ castInsertionExpr refts myr e
  Type{} -> expr
  Coercion{} -> expr

castInsertionAlt :: Refinements -> SReft -> CoreAlt -> CoreAlt
castInsertionAlt refts tgr (con, xs, e) = (con, xs, e'')
  where
    e' = castInsertionExpr refts myr e
    myr = exprReft refts tgr e'
    e'' = if any F.isGradual [myr, tgr] then insertCast myr tgr e' else e'


-- Constructing the casts

-- reftToCoreExpr :: Reft -> CoreExpr
-- reftToCoreExpr = undefined
