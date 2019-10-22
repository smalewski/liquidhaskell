{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances    #-}
module Language.Haskell.Liquid.Synthesize.GHC where

import CoreSyn (CoreExpr)
import qualified CoreSyn as GHC
import qualified Data.HashMap.Strict as M
import           Language.Fixpoint.Types hiding (SEnv, SVar, Error)
import qualified Language.Fixpoint.Types        as F 
import qualified Language.Fixpoint.Types.Config as F
import           Language.Haskell.Liquid.Types hiding (SVar)
import Var 
import TyCoRep
import CoreSyn

import IdInfo
import OccName
import Unique 
import Name 
import TysPrim


import Data.Default
import Data.Maybe (fromMaybe)
import           Data.List 
import Language.Haskell.Liquid.GHC.TypeRep
import Language.Fixpoint.Types
import Debug.Trace
import qualified Data.HashMap.Strict as M

instance Default Type where
    def = TyVarTy alphaTyVar 
    
-- JP: Let's try to avoid this.
-- instance Default CoreExpr where 
--     def = Var $ mkVar (Just "undefined") 0 def

mkVar :: Maybe String -> Int -> Type -> Var
mkVar x i t = mkGlobalVar VanillaId name t vanillaIdInfo 
  where 
    name = mkSystemName (mkUnique 'S' i) (mkVarOcc x')
    x'   = fromMaybe (freshName i) x 

freshName :: Int -> String 
freshName i = "lSyn$" ++ show i 

-- Select all functions with result type equal with goalType
--        | goal |
goalType :: Type -> Type -> Bool
goalType τ t@(ForAllTy (TvBndr var _) htype) = 
  let substHType = substInType htype (varsInType τ)
  in  goalType τ substHType
goalType τ t@(FunTy _ t'') -- τ: base types
  | t'' == τ  = True
  | otherwise = goalType τ t''
goalType τ                 t 
  | τ == t    = True
  | otherwise = False


-- Subgoals are function's arguments.
createSubgoals :: Type -> [Type] 
createSubgoals (ForAllTy _ htype) = createSubgoals htype
createSubgoals (FunTy t1 t2)      = t1 : createSubgoals t2
createSubgoals t                  = [t]


-- Removes forall from type and replaces
-- type variables from the first argument to the second argument.
-- Returns the new type.
-- TODO: Instead of substituting type variables, perform type applications
-- and then, get the type.
instantiateType :: Type -> Type -> Type 
instantiateType τ t = 
  let t' = substInType t (varsInType τ)
  in  case t' of 
        ForAllTy _ t'' -> t''
        _              -> t' 

-- TODO: More than one type variables in type (what happens in forall case with that?).
-- use Language.Haskell.Liquid.GHC.TypeRep.subst instead 
substInType :: Type -> [TyVar] -> Type 
substInType t []   = t
substInType t [tv] = substInType' tv t
  where 
    substInType' tv (TyVarTy var)                = TyVarTy tv
    substInType' tv (ForAllTy (TvBndr var x) ty) = ForAllTy (TvBndr tv x) (substInType' tv ty)
    substInType' tv (FunTy t0 t1)                = FunTy (substInType' tv t0) (substInType' tv t1)
    substInType' tv (AppTy t0 t1)                = AppTy (substInType' tv t0) (substInType' tv t1)
    substInType' tv (TyConApp c ts)              = TyConApp c (map (substInType' tv) ts)
    substInType' _  t                            = error $ "[substInType'] Shouldn't reach that point for now " ++ showTy t
substInType _ vars = error $ "My example has one type variable. Vars: " ++ show (map symbol vars)

-- Find all variables in type
varsInType :: Type -> [TyVar] 
varsInType t = (map head . group . sort) (varsInType' t)
  where
    varsInType' (TyVarTy var)                = [var]
    varsInType' (ForAllTy (TvBndr var _) ty) = var : varsInType' ty
    varsInType' (FunTy t0 t1)                = varsInType' t0 ++ varsInType' t1
    varsInType' (AppTy t0 t1)                = varsInType' t0 ++ varsInType' t1 
    varsInType' (TyConApp c ts)              = foldr (\x y -> concatMap varsInType' ts ++ y) [] ts
    varsInType' t                            = error $ "[varsInType] Shouldn't reach that point for now " ++ showTy t

fromAnf :: CoreExpr -> CoreExpr
fromAnf e = fst $ fromAnf' e []

-- If you find a binding add it to the second argument.
--                    | (lhs, rhs)      |
fromAnf' :: CoreExpr -> [(Var, CoreExpr)] -> (CoreExpr, [(Var, CoreExpr)])
fromAnf' (Let bnd e) bnds       = 
  case bnd of
    Rec {}       -> error "No recursive bindings in let."
    NonRec rb lb -> 
      fromAnf' e ((rb, replaceBnds lb' bnds') : bnds')
        where (lb', bnds')     = fromAnf' lb bnds
fromAnf' (Case scr bnd tp alts) bnds
  = (Case scr bnd tp (map (\(altc, xs, e) -> (altc, xs, fst $ fromAnf' e bnds)) alts), bnds)
fromAnf' e           bnds       = (replaceBnds e bnds, bnds)


replaceBnds :: CoreExpr -> [(Var, CoreExpr)] -> CoreExpr 
replaceBnds (Var var) bnds    = fromMaybe (Var var) (lookup var bnds)
replaceBnds (App e1 e2) bnds  = App (replaceBnds e1 bnds) (replaceBnds e2 bnds) 
replaceBnds (Type t)    _     = Type t
replaceBnds lit@Lit{}   _     = lit 
replaceBnds e           _     = e

------------------------------------------------------------------------------------------------
-------------------------------------- Handle REnv ---------------------------------------------
------------------------------------------------------------------------------------------------
-- Duplicate from Monad due to dependencies between modules.
type SSEnv = M.HashMap Symbol (SpecType, Var)

--                                      | Current top-level binding |
filterREnv :: M.HashMap Symbol SpecType -> Var -> M.HashMap Symbol SpecType
filterREnv renv tlVar = 
  let renv_lst  = M.toList renv
      renv_lst' = filter (\(_, specT) -> 
        let ht = toType specT
        in  showTy ht /= "(RApp   GHC.Prim.Addr# )") renv_lst
  in  M.fromList renv_lst'

getTopLvlBndrs :: GHC.CoreProgram -> [Var]
getTopLvlBndrs = 
  map (\cb -> 
    case cb of 
      GHC.NonRec b _ -> b
      GHC.Rec{} -> error $ " [ getTopLvlBndrs ] Rec "
  )

--                       | Current top-level binder |
varsP :: GHC.CoreProgram -> Var -> (GHC.CoreExpr -> [Var]) -> [Var]
varsP cp tlVar f = 
  case filter (\cb -> isInCB cb tlVar) cp of
    [cb] -> varsCB cb f
    _    -> error " Every top-level corebind must be unique! "

isInCB :: GHC.CoreBind -> Var -> Bool
isInCB (GHC.NonRec b e) tlVar = b == tlVar 
isInCB (GHC.Rec {}) _ = error " [ isInCB ] Rec binder. "

varsCB :: GHC.CoreBind -> (GHC.CoreExpr -> [Var]) -> [Var]
varsCB (GHC.NonRec b e) f = f e
varsCB (GHC.Rec ls) _ = trace " [ symbolToVarCB ] Rec " []

varsE :: GHC.CoreExpr -> [Var]
varsE (GHC.Lam a e) = a : varsE e
varsE (GHC.Let (GHC.NonRec b _) e) = b : varsE e
varsE (GHC.Case eb b _ alts) = foldr (\(_, vars, e) res -> vars ++ (varsE e) ++ res) [b] alts
varsE (GHC.Tick _ e) = varsE e
varsE e = []

caseVarsE :: GHC.CoreExpr -> [Var] 
caseVarsE (GHC.Lam a e) = caseVarsE e 
caseVarsE (GHC.Let (GHC.NonRec b _) e) = caseVarsE e
caseVarsE (GHC.Case eb b _ alts) = foldr (\(_, vars, e) res -> caseVarsE e ++ res) [b] alts 
caseVarsE (GHC.Tick _ e) = caseVarsE e 
caseVarsE e = [] 

symbolToVar :: GHC.CoreProgram -> Var -> M.HashMap Symbol SpecType -> SSEnv
symbolToVar cp tlBndr renv = trace (" CaseVars " ++ show (varsP cp tlBndr caseVarsE)) $ 
  let vars = [(F.symbol x, x) | x <- varsP cp tlBndr varsE]
      casevars = [F.symbol x | x <- varsP cp tlBndr caseVarsE]
      tlVars = [(F.symbol x, x) | x <- getTopLvlBndrs cp]
      symbolVar x = fromMaybe (fromMaybe (error $ " [ symbolToVar ] impossible ") $ lookup x tlVars) $ lookup x vars
      renv' = foldr (\s hm -> M.delete s hm) renv casevars
  in  M.fromList [ (s, (t, symbolVar s)) | (s, t) <- M.toList renv']

argsP :: GHC.CoreProgram -> Var -> [Var] 
argsP []         tlVar = error $ " [ argsP ] " ++ show tlVar
argsP (cb : cbs) tlVar 
  | isInCB cb tlVar = argsCB cb
  | otherwise = argsP cbs tlVar

argsCB :: GHC.CoreBind -> [Var]
argsCB (GHC.NonRec b e) = argsE e 

argsE :: GHC.CoreExpr -> [Var]
argsE (GHC.Lam a e) = a : argsE e 
argsE (GHC.Let (GHC.NonRec b _) e) = argsE e
argsE _ = [] 
