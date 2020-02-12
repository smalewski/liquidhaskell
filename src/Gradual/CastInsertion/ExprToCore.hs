{-# OPTIONS_GHC -Wwarn #-}
module Gradual.CastInsertion.ExprToCore where
-- module Gradual.CastInsertion.ExprToCore (
--   exprToCore,
--   ) where

import           Debug.Trace                         (trace)
import           Control.Monad.State
import           CoreSyn                             hiding (Expr)
import           CoreUtils
import           Data.Text                           (unpack)
import           Id
import           Type
import           Name
import           UniqSupply
-- import CoreUtils
import           Control.Monad.Trans.Class           (lift)
import qualified CoreMonad                           as CM
import           Data.Maybe                          (fromMaybe)
import           DynFlags
import           HscTypes                            hiding (Target)
import           Coercion
import           MkCore
import           Module
import           OccName
import           Outputable                          (PrintUnqualified)
import           PrelNames
import           SrcLoc                              (SrcSpan)
import           SrcLoc                              (noSrcSpan)
import           TysWiredIn
-- import qualified Data.Text as T

import           Language.Haskell.Liquid.Misc
-- import Language.Haskell.Liquid.WiredIn
import           Gradual.CastInsertion.Monad
import           Language.Fixpoint.SortCheck         hiding (sortExpr)
import qualified Language.Fixpoint.Types             as F
import           Language.Fixpoint.Types             (Sort (..))
import           Language.Fixpoint.Types.Refinements
import           Language.Haskell.Liquid.Bare.Lookup
import           Language.Haskell.Liquid.Types       hiding (R)
import           Language.Haskell.Liquid.Types.RefType     (toType, rTypeSortedReft)
import           Language.Haskell.Liquid.GHC.Misc                      (showCBs)

specToCore :: SpecType -> ToCore CoreExpr
specToCore spec = do
  let ty = toType spec
  vId <- freshId ty
  embTC <- tyConEnv
  let RR s (Reft(v, e)) = ungrad $ rTypeSortedReft embTC spec
  insertLocalId v vId
  insertSymSort v s
  exprToCore e

exprToCore :: Expr -> ToCore CoreExpr
exprToCore (ESym s) = error $ "Sym: " ++ show s
exprToCore (ECon c) =
  case c of
    I n     -> mkIntegerExpr n
    R x     -> pure $ mkDoubleExpr x
    L str _ -> mkStringExpr $ unpack str -- FIXME
exprToCore (EVar x) = Var <$> lookupTCId x
exprToCore (EApp e1 e2) = appToCore e1 e2
exprToCore (ENeg e) = negToCore e
exprToCore (EBin op e1 e2) = binToCore op e1 e2
exprToCore (EIte p t f) = iteToCore p t f
exprToCore (ECst e s) = castToCore e s
exprToCore (ELam (x, s) e) = lamToCore x s e
exprToCore (ETApp e s) = exprToCore e -- FIXME
exprToCore (PAnd es) = andToCore es
exprToCore (POr es) = orToCore es
exprToCore (PNot e) = notToCore e
exprToCore (PImp e1 e2) = impToCore e1 e2
exprToCore (PIff e1 e2) = iffToCore e1 e2
exprToCore (PAtom rel e1 e2) = atomToCore rel e1 e2
exprToCore (ETAbs e _) = exprToCore e
exprToCore (PGrad _ _ _ e) = exprToCore e -- error "Can't insert casts in gradual expressions."
exprToCore (PKVar kv sub) = error $ "KVar " ++ show kv ++ " SUBS " ++ show sub
exprToCore (PAll xs e) = error "Cast insetion is not possible in predicates with universal quantifiers."
exprToCore (PExist xs e) = error "Cast insertion is not possible in predicates with existential quantifiers."

appToCore :: Expr -> Expr -> ToCore CoreExpr
appToCore e1 e2 = mkCoreApps <$> (exprToCore e1) <*> sequence [exprToCore e2]

negToCore :: Expr -> ToCore CoreExpr
negToCore e = do
  negId <- lookupTCId "GHC.Classes.not"
  ce <- exprToCore e
  pure $ mkCoreApps (Var negId) [ce]

castToCore :: Expr -> F.Sort -> ToCore CoreExpr
castToCore e s = do
  -- let fromSort = sortExpr  F.emptySEnv e
  -- let fromTy = sortType fromSort
  toTy <- sortType s
  idn <- freshId toTy
  let coer = mkCoVarCo idn
  expr <- exprToCore e
  pure $ mkCast expr coer

sortType :: Sort -> ToCore Type
sortType FInt = pure intTy
sortType FReal = pure doubleTy
sortType FNum = error "num"
sortType FFrac = error "frac"
sortType (FObj x) = do
  idx <- lookupTCId x
  pure $ idType idx
sortType (FVar n) = error "var"
sortType (FFunc s1 s2) = do
  t1  <- sortType s1
  t2  <- sortType s2
  var <- freshId t1
  pure $ mkLamType var t2
sortType (FAbs n s) = error "abs"
sortType (FTC tc) = error "tc"
sortType (FApp s1 s2) = do
  t1 <- sortType s1
  t2 <- sortType s2
  pure $ mkAppTy t1 t2

ftcType :: F.FTycon -> ToCore Type
ftcType ftc = do
  mtc <- tyconFTycon ftc
  fname <- lookupTCName ftc
  case mtc of
    Nothing -> mkTyConTy <$> lookupTyCon fname
    Just tc -> pure $ mkTyConTy tc

lamToCore :: F.Symbol -> F.Sort -> Expr -> ToCore CoreExpr
lamToCore x s e = do
  insertSymSort x s
  let occ = mkVarOcc $ F.symbolString x
  ty <- sortType s
  uniq <- getUniqueM
  let name = mkInternalName uniq occ noSrcSpan
  let b = mkLocalId name ty
  ec <- exprToCore e
  pure $ mkCoreLams [b] ec

iteToCore :: Expr -> Expr -> Expr -> ToCore CoreExpr
iteToCore p t f = do
  p' <- exprToCore p
  t' <- exprToCore t
  f' <- exprToCore f
  pure $ mkIfThenElse p' t' f'

andToCore :: [Expr] -> ToCore CoreExpr
andToCore es = do
  ces <- traverse exprToCore es
  andCore ces

orToCore :: [Expr] -> ToCore CoreExpr
orToCore es = do
  ces <- traverse exprToCore es
  orCore ces

andCore :: [CoreExpr] -> ToCore CoreExpr
andCore es = do
  and <- Var <$> lookupTCId "GHC.Classes.&&"
  idn <- freshId anyTy
  let true = Var trueDataConId
  let expr = inter and true es
  _ <- trace (showCBs False [NonRec idn expr]) $ pure ()
  pure expr

orCore :: [CoreExpr] -> ToCore CoreExpr
orCore es = do
  or <- Var <$> lookupTCId "GHC.Classes.||"
  let false = Var falseDataConId
  pure $ inter or false es

impToCore :: Expr -> Expr -> ToCore CoreExpr
impToCore e1 e2 = do
  -- ~ec1 \/ ec2
  nec1 <- notToCore e1
  ec2 <- exprToCore e2
  orCore [nec1, ec2]

iffToCore :: Expr -> Expr -> ToCore CoreExpr
iffToCore e1 e2 = do
  right <- impToCore e1 e2
  left <- impToCore e2 e1
  andCore [left, right]

notToCore :: Expr -> ToCore CoreExpr
notToCore e = do
  ec <- exprToCore e
  no <- Var <$> lookupTCId "GHC.Classes.not"
  pure $ mkCoreApps no [ec]

binToCore :: Bop -> Expr -> Expr -> ToCore CoreExpr
binToCore op e1 e2 = do
  sort <- sortExpr e1
  opVar <- opToVar op sort
  ec1 <- exprToCore e1
  ec2 <- exprToCore e2
  pure $ mkCoreApps opVar [ec1, ec2]

sortExpr :: Expr -> ToCore F.Sort
sortExpr expr = do
  env <- symSortEnv
  let mSort = checkSortExpr env expr
  let sort  = fromMaybe (F.FObj $ F.symbol "Unknown") mSort
  pure sort

atomToCore :: Brel -> Expr -> Expr -> ToCore CoreExpr
atomToCore rel e1 e2 = do
  sort <- sortExpr e1
  var <- relToVar rel sort
  ec1 <- exprToCore e1
  ec2 <- exprToCore e2
  pure $ mkCoreApps var [ec1, ec2]

relToVar :: Brel -> F.Sort -> ToCore CoreExpr
relToVar rel sort = Var <$> relId rel sort

opToVar :: Bop -> F.Sort -> ToCore CoreExpr
opToVar op sort = Var <$> opId op sort

inter :: CoreExpr -> CoreExpr -> [CoreExpr] -> CoreExpr
inter _ z []     = z
inter f z (x:xs) = mkCoreApps f [x, inter f z xs]

relId :: Brel -> F.Sort -> ToCore Id
relId Eq s
  | F.isNumeric s = lookupId eqIntegerPrimName
  | F.isReal s = lookupId eqName
  | F.isString s = lookupId eqStringName
  | otherwise = lookupId eqTyConName
relId Ne s
  | F.isNumeric s = lookupId neqIntegerPrimName
  | otherwise     = lookupTCId "/="
relId Gt s
  | F.isNumeric s = lookupId gtIntegerPrimName
  | otherwise     = lookupTCId ">"
relId Ge s
  | F.isNumeric s = lookupId geIntegerPrimName
  | otherwise     = lookupId geName
relId Lt s
  | F.isNumeric s = lookupId ltIntegerPrimName
  | otherwise     = lookupTCId "<"
relId Le s
  | F.isNumeric s = lookupId leIntegerPrimName
  | otherwise     = lookupTCId "<="
relId Ueq s = lookupId eqTyConName
relId Une s = lookupId eqTyConName -- FIXME

opId :: Bop -> F.Sort -> ToCore Id
opId Plus s
  | F.isNumeric s = lookupId plusIntegerName
  | otherwise      = lookupTCId "GHC.Num.+"
opId Minus s
  | F.isNumeric s = lookupId minusIntegerName
  | otherwise     = lookupId minusName
opId Times s
  | F.isNumeric s = lookupId timesIntegerName
  | otherwise     = lookupTCId "GHC.Num.*"
opId Div s
  | F.isNumeric s = lookupId divIntegerName
  | otherwise     = lookupTCId "GHC.Num./"
opId Mod s
  | F.isNumeric s = lookupId modIntegerName
  | otherwise     = lookupTCId "GHC.Num.mod"
opId RTimes s     = lookupTCId "GHC.Num.*"
opId RDiv s       = lookupTCId "GHC.Num./"

lookupTCName :: F.Symbolic a => a -> ToCore Name
lookupTCName s = do
  hscEnv <- getHEnv
  mod <- getModule
  let moduleName' = moduleName mod
  let modName = ModName Target moduleName'
  let namespace = Just varName
  let sym = F.symbol s
  let locsym = F.dummyLoc sym
  names <- liftIO $ lookupName hscEnv modName namespace locsym
  printMsg $ show names
  case nubHashOn showpp names of
    [x] -> pure x
    _   -> error $  "Multiple names for " ++ show (F.symbol s)
      ++ ": " ++  (show $ F.symbol <$> names)

lookupTCId :: F.Symbolic a => a -> ToCore Id
lookupTCId s = do
  lid  <- lookupLocalId s
  case lid of
    Nothing -> lookupTCName s >>= lookupId
    Just idx -> pure idx





