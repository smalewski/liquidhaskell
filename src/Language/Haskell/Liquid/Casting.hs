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

-- DEBUGGING STUFF

-- specToReft :: SpecType -> [Reft]
-- specToReft = map F.toReft . specToRReft

-- specToRReft :: SpecType -> [RReft]
-- specToRReft (RVar _ r) = [r]
-- specToRReft (RFun _ i o r) = r : specToRReft i ++ specToRReft o
-- specToRReft (RApp _ _ _ r) = [r]
-- specToRReft (RAppTy _ _ r) = [r]
-- specToRReft _ = []


-- printCoresRaw :: [GhcInfo] -> IO ()
-- printCoresRaw gs = putStrLn "CoreRaw" *> mapM_ (putStrLn . showCBs True . cbs) gs

-- printCores :: [GhcInfo] -> IO ()
-- printCores gs = putStrLn "Core" *> mapM_ (mapM_ (printBind 0 . symbolBind) . cbs) gs

-- printCoress :: [CoreBind] -> IO ()
-- printCoress gs = putStrLn "Core" *> mapM_ (printBind 0 . symbolBind) gs

-- printBinds :: [CGInfo] -> IO ()
-- printBinds cgs = do putStrLn "Binds"
--                     mapM_ printB cgs
--                     putStrLn "STRATUM"
--                     mapM_ printS cgs
--                     print $ map (isEmpty . sCs) cgs
--   where
--     sortByID = sortOn (\(x,_,_) -> x)
--     printB = mapM_ print . sortByID . F.bindEnvToList . binds
--     printS = mapM_ (print . senv) . sCs
--     isEmpty [] = True
--     isEmpty _ = False

-- symbolExpr :: Symbolic a => Expr a -> Expr Symbol
-- symbolExpr (Var x) = Var x
-- symbolExpr (Lit l) = Lit l
-- symbolExpr (App e1 e2) = App (symbolExpr e1) (symbolExpr e2)
-- symbolExpr (Lam a e) = Lam (F.symbol a) (symbolExpr e)
-- symbolExpr (Let b e) = Let (symbolBind b) (symbolExpr e)
-- symbolExpr (Case e a t cs) = Case (symbolExpr e) (F.symbol a) t (symbolCase <$> cs)
-- symbolExpr (Cast e c) = Cast (symbolExpr e) c
-- symbolExpr (Tick tk e) = Tick tk (symbolExpr e)
-- symbolExpr (Type t) = Type t
-- symbolExpr (Coercion c) = Coercion c

-- symbolBind :: Symbolic a => Bind a -> Bind Symbol
-- symbolBind (NonRec a e) = NonRec (F.symbol a) (symbolExpr e)
-- symbolBind (Rec bs) = Rec $ bimap F.symbol symbolExpr <$> bs

-- symbolCase :: Symbolic a => Alt a -> Alt Symbol
-- symbolCase (ctr, as, e) = (ctr, F.symbol <$> as, symbolExpr e)

-- printExpr :: Show a => Int -> Expr a -> IO ()
-- printExpr n (Var x) = putStrLn $ replicate n '-' ++ "Var " ++ (show $ F.symbol x)
-- printExpr n (Lit _) = putStrLn $ replicate n '-' ++ "Lit "
-- printExpr n (App e1 e2) = do putStrLn $ replicate n '-' ++ "App"
--                              printExpr (n+1) e1
--                              printExpr (n+1) e2
-- printExpr n (Lam a e) = do putStrLn $ replicate n '-' ++ "Lam " ++ show a
--                            printExpr (n+1) e
-- printExpr n (Let b e) = do putStrLn $ replicate n '-' ++ "Let "
--                            printBind (n+1) b
--                            printExpr (n+1) e
-- printExpr n (Case e a _ cs) = do putStrLn $ replicate n '-' ++ "Case"
--                                  printExpr (n+1) e
--                                  putStrLn $ replicate (n+1) '-' ++ show a
--                                  mapM_ (printCase (n+1)) cs
-- printExpr n (Cast e _) = do putStrLn $ replicate n '-' ++ "Cast "
--                             printExpr (n+1) e
-- printExpr n (Tick _ e) = printExpr n e
-- printExpr n _ = putStrLn $ replicate n '-' ++ " ."

-- printBind :: Show a => Int -> Bind a -> IO ()
-- printBind n (NonRec a e) = do putStrLn $ replicate n '-' ++ "NonRec " ++ show a
--                               printExpr (n+1) e
-- printBind n (Rec bs) = do putStrLn $ replicate n '-' ++ "Rec"
--                           mapM_ (printRec (n+1)) bs
--   where printRec n (b,e) = do putStrLn $ replicate n '-' ++ show b
--                               printExpr (n+1) e
-- printCase :: Show a => Int -> Alt a -> IO ()
-- printCase n (_, as, e) = do putStrLn $ replicate n '-' ++ "VC" ++ show as
--                             printExpr (n+1) e

-- showRT :: Show r => Int -> RType c tv r -> String
-- showRT n (RVar _ p) = depth n $ "RVAR " ++ show p
-- showRT n (RFun x i o p) = depth n $ "RFUN " ++ show x ++ ":" ++ show p ++ showRT (n+1) i ++ " -> " ++ showRT (n+1) o
-- showRT n (RAllT _ r) = depth n $ "RALLT " ++ showRT (n+1) r
-- showRT n (RAllP _ r) = depth n $ "RALLP " ++ showRT (n+1) r
-- showRT n (RAllS s r) = depth n $ "RAllS " ++ show s ++  ":" ++ showRT (n+1) r
-- showRT n (RApp _ as pas p) = depth n $ "RApp " ++ show p ++ unlines (map (showRT (n+1)) as) ++ unlines (map (showRP (n+1)) pas)
-- showRT n (RAllE s a r) = depth n $ "RALLE " ++ show s ++ ":" ++ showRT (n+1) a ++ showRT (n+1) r
-- showRT n (REx s a r) = depth n $ "REX " ++ show s ++ ":" ++ showRT (n+1) a ++ showRT (n+1) r
-- showRT n (RExprArg le) = depth n $ "REXPRARG " ++ show le
-- showRT n (RAppTy a r p) = depth n $ "RAPPTY " ++ show p ++ showRT (n+1) a ++ showRT (n+1) r
-- showRT n (RRTy env p _ r) = depth n $ "RRTY " ++ show p ++ unlines (map (showSRT (n+1)) env) ++ "finenv" ++ showRT (n+1) r
-- showRT n (RHole p) = depth n $ "RHOLE " ++  show p

-- showRP :: Show r => Int -> RTProp c tv r -> String
-- showRP n (RProp as b) = depth n $ "PROP " ++ unlines (map (showSRT (n+1)) as) ++ showRT (n+1) b

-- showSRT :: Show r => Int -> (Symbol, RType c tv r) -> String
-- showSRT n (s, r) = depth n $ "( " ++ show s ++ " , " ++ showRT (n+1) r ++ ")"

-- depth :: Int -> String ->  String
-- depth n s = "\n" ++ replicate (n*2) '-' ++ s

-- printRefts :: Refinements -> IO()
-- printRefts r = mapM_ print $ M.toList r
