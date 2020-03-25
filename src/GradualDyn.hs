{-# LANGUAGE TupleSections #-}
{-# LANGUAGE BangPatterns  #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Main where

-- import           UniqSupply       (mkSplitUniqSupply)
-- import           DynFlags hiding (getOpts)
-- import           Module
-- import           Outputable (alwaysQualify)
-- import           Rules (emptyRuleBase)
-- import           System.Console.CmdArgs.Verbosity hiding (Loud)
-- import           HscMain
-- import           HscTypes
-- import           MkIface
-- import           Data.Bifunctor
-- import           DriverPipeline

-- import Language.Haskell.Liquid.Types
-- import Language.Haskell.Liquid.Constraint.Types (CGInfo(..)) -- , FixWfC, SubC(..), CGEnv(..))
-- import Language.Haskell.Liquid.UX.Config (Config(..))
-- import Language.Haskell.Liquid.UX.CmdLine (getOpts, exitWithResult)
-- import Language.Haskell.Liquid.Constraint.ToFixpoint (cgInfoFInfo, fixConfig)
-- import Language.Haskell.Liquid.GHC.Interface
-- import           Language.Haskell.Liquid.Constraint.Generate
-- import           Language.Haskell.Liquid.UX.Tidy

-- import qualified Language.Fixpoint.Types as F
-- import qualified Language.Fixpoint.Types.Config as F
-- import           Language.Fixpoint.Solver       (simplifyFInfo, resultExit)
-- import           Language.Fixpoint.Solver.Solve (solve)
-- import qualified Language.Fixpoint.Solver.GradualSolution as GS
-- import           Language.Fixpoint.Misc
-- import           Language.Fixpoint.Graph.Partition (partition')

-- import System.Exit                    (ExitCode, exitWith, exitSuccess, exitFailure)
-- import System.FilePath (replaceExtension)
-- import System.Environment             (getArgs)
-- import Control.Monad (when, unless) 
-- import Control.Monad.IO.Class (liftIO) 
-- import qualified Control.Exception as Ex

-- import qualified Data.List as L 

-- import Gradual.Log 
-- import Gradual.Concretize 
-- import Gradual.Types
-- -- import Gradual.Misc (mapMWithLog)
-- import Gradual.Uniquify
-- import Gradual.Refinements
-- import Gradual.PrettyPrinting
-- -- import qualified Gradual.GUI as GUI
-- import qualified Gradual.Trivial as T 
-- import Gradual.Match 
-- import Gradual.CastInsertion

import qualified Gradual.Interface.GHCMain as GHCMain

main :: IO ()
main = GHCMain.main

-- main :: IO a
-- main = do
--   cfg   <- getArgs >>= getOpts
--   cgss <- quietly $ liquidConstraintsAndGuts (cfg{gradual=True, eliminate = F.None})
--   case cgss of
--     Left (cgigs) -> mapM runGradual cgigs >> exitSuccess
--     Right e              -> exitWith e

-- liquidConstraintsAndGuts :: Config -> IO (Either [(CGInfo, ModGuts, ModSummary)] ExitCode)
-- liquidConstraintsAndGuts cfg = do
--   z <- actOrDie $ second Just <$> getInfoAndGuts Nothing cfg (files cfg)
--   case z of
--     Left e -> do
--       exitWithResult cfg (files cfg) $ mempty { o_result = e }
--       return $ Right $ resultExit e
--     Right (gigs, _) -> do
--       let f (cgi, mg, ms) = (generateConstraints cgi, mg, ms)
--       return $ Left $ map f gigs

-- actOrDie :: IO a -> IO (Either ErrorResult a)
-- actOrDie act =
--     (Right <$> act)
--       `Ex.catch` (\(e :: SourceError) -> handle e)
--       `Ex.catch` (\(e :: Error)       -> handle e)
--       `Ex.catch` (\(e :: UserError)   -> handle e)
--       `Ex.catch` (\(e :: [Error])     -> handle e)

-- handle :: (Result a) => a -> IO (Either ErrorResult b)
-- handle = return . Left . result

-- hscCompileModGuts :: HscEnv -> ModSummary
--                   -> ModGuts -> FilePath -> IO ()
-- hscCompileModGuts hsc_env mod_summary guts output_filename
--   = runHsc hsc_env $ do
--         (iface, changed, _details, cgguts) <- hscNormalIface' guts Nothing
--         liftIO $ hscWriteIface (hsc_dflags hsc_env) iface changed mod_summary
--         _ <- liftIO $ hscGenHardCode hsc_env cgguts mod_summary output_filename
--         return ()

-- hscWriteIface :: DynFlags -> ModIface -> Bool -> ModSummary -> IO ()
-- hscWriteIface dflags iface no_change mod_summary = do
--     let ifaceFile = ml_hi_file (ms_location mod_summary)
--     unless no_change $
--         {-# SCC "writeIface" #-}
--         writeIfaceFile dflags ifaceFile iface
--     whenGeneratingDynamicToo dflags $ do
--         -- TODO: We should do a no_change check for the dynamic
--         --       interface file too
--         -- TODO: Should handle the dynamic hi filename properly
--         let dynIfaceFile = replaceExtension ifaceFile (dynHiSuf dflags)
--             dynIfaceFile' = addBootSuffix_maybe (mi_boot iface) dynIfaceFile
--             dynDflags = dynamicTooMkDynamicDynFlags dflags
--         writeIfaceFile dynDflags dynIfaceFile' iface


-- runGradual :: (CGInfo, ModGuts, ModSummary) -> IO [(GSub F.GWInfo,F.Result (Integer, Cinfo))]
-- runGradual (cgi, modGuts, modSummary) = do
--   let cfg      = (getConfig cgi){gradual=True}
--   logDepth (gdepth cfg)
--   let fname    = target (ghcI cgi)
--   let fcfg     = fixConfig fname cfg
--   finfo       <- quietly $ cgInfoFInfo (ghcI cgi) cgi
--   let tx       = if (gsimplify cfg) then T.simplify else id
--   sinfo <- (uniquify . tx) <$> (quietly $ simplifyFInfo fcfg finfo)
--   logSpans (fst sinfo)
--   parts <- logParts $ partition' Nothing (snd sinfo)
--   let (gsis, sis) = L.partition F.isGradual parts
--   logGParts gsis
--   let gcfg     = (makeGConfig cfg) {pNumber = length gsis}
--   sol <- mconcat <$> (quietly $ mapM (solve fcfg) sis)
--   let gcfgs = setPId gcfg <$> [1..(length gsis)]
--   -- solss <- mapMWithLog "Running Partition" (uncurry $ solveSInfo fcfg) (zip gcfgs gsis)
--   solss <- mapM (uncurry $ solveSInfo fcfg) (zip gcfgs gsis)
--   when (not $ F.isSafe sol) $ do

--     when (length solss == 0) $ do
--       putStrLn "The static part cannot be satisfied: UNSAFE"
--       logMatches $ matchSolutions (fst sinfo) solss
--       printLog
--       exitFailure

--     let hscEnv = env $ ghcI cgi
--     -- (_, modGuts') <- castCore cgi modGuts
--     let df'=  hsc_dflags hscEnv
--     let df =  df' { ghcLink      = LinkBinary
--                   , hscTarget    = HscAsm
--                   , ghcMode      = OneShot
--                   }
--     let hscEnv' = hscEnv { hsc_dflags = df }
--     let fout = "out.o"

--     hscCompileModGuts hscEnv' modSummary modGuts fout
--     linkBinary df [fout] []
--   exitSuccess



-- solveSInfo :: F.Config  -> GConfig -> F.SInfo Cinfo -> IO [GSub F.GWInfo]
-- solveSInfo !fcfg !gcfg !sinfo = do 
--   gmap     <- makeGMap gcfg fcfg sinfo $ GS.init fcfg sinfo 
--   allgs    <- logConcr $ concretize gmap sinfo
--   putStrLn ("Total number of concretizations: " ++ show (length $ map snd allgs))
--   when ((length $ map snd allgs) > 1000000) $ do 
--      putStrLn ("Too many concretizations found. Aborting!") 
--      logAbord
--      printLog
--      exitFailure
--   res   <- solveWhile fcfg 1001 (take 1000 allgs)
--   -- res   <- quietly $ mapM (solve' fcfg) (zip allgs [1..])
--   case res of 
--     (x:xs) -> do putStrLn ("[" ++ show (1 + length xs) ++ "/" ++ (show $ length allgs) ++ "] Solutions Found!" ++ if length xs > 0 then " e.g.," else "") 
--                  putStrLn (pretty $ (map (mapSnd snd) $ fromGSub $ fst x))
--                  logSol (x:xs)
--                  return (fst <$> (x:xs))
--     _     -> do putStrLn ((show $ length allgs) ++ "] Solutions. UNSAFE!\n")  
--                 whenLoud $ putStrLn ("UNSAFE PARTITION: " ++ show sinfo)  
--                 logSol ([])
--                 return [mempty] 

-- solveWhile :: F.Config -> Int -> [(a, F.SInfo Cinfo)] -> IO [(a, F.Result (Integer, Cinfo))]
-- solveWhile cfg m xs = go [] xs
--   where
--     go !acc [] = return acc 
--     go !acc ((x, y):xs) = do 
--       r <- solve cfg y 
--       if F.isSafe r then
--          if length acc == m -1 
--             then return ((x,r):acc)
--             else go ((x,r):acc) xs 
--       else go acc xs
  


-- quietly :: IO a -> IO a 
-- quietly act = do 
--   vb <- getVerbosity 
--   setVerbosity Quiet
--   r  <- act 
--   setVerbosity vb 
--   return r 
