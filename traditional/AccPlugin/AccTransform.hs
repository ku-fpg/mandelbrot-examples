{-# LANGUAGE PatternSynonyms            #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE CPP                        #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE TypeSynonymInstances       #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TupleSections              #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveFoldable             #-}
{-# LANGUAGE DeriveTraversable          #-}

module AccPlugin.AccTransform (plugin) where

import           GhcPlugins

import           Data.Array.Accelerate hiding (map, (++), not, filter, fst, snd)
import qualified Data.Array.Accelerate as A

import           Control.Monad

import           HERMIT.Name (newIdH)
import           HERMIT.Monad (LiftCoreM (..))
import           HERMIT.GHC.Typechecker (initTcFromModGuts)

import           Language.KURE
import           Language.KURE.MonadCatch

import           Control.Monad.IO.Class

import           TcRnTypes
import           TcRnMonad
import           TcSMonad
import           TcSimplify
import           TcEvidence
import           FamInst
import           FamInstEnv
import           DsBinds
import           DsMonad (initDsTc)

import           Encoding (zEncodeString)

import           UniqDFM

import           Control.Arrow (first, second)
import           Data.Char (isSpace)

import           ErrUtils
import           Pair
import           Class

import           Control.Monad.Reader

import           Data.List (partition)
import           Data.Maybe (fromMaybe, isJust)

import qualified Language.Haskell.TH.Syntax as TH

data PluginEnv
    = PluginEnv
      { pluginModGuts :: ModGuts
      }

newtype PluginM a = PluginM { runPluginM :: ReaderT PluginEnv CoreM a }
    deriving (Functor, Applicative, Monad
             ,MonadIO, MonadReader PluginEnv)

instance MonadThings PluginM where
  lookupThing   = liftCoreM . lookupThing
  lookupId      = liftCoreM . lookupId
  lookupDataCon = liftCoreM . lookupDataCon
  lookupTyCon   = liftCoreM . lookupTyCon

class HasHscEnv m where
  getHscEnv' :: m HscEnv

instance HasHscEnv CoreM where
  getHscEnv' = getHscEnv

instance HasHscEnv PluginM where
  getHscEnv' = liftCoreM getHscEnv'

instance MonadUnique PluginM where
  getUniqueSupplyM = liftCoreM getUniqueSupplyM

instance HasDynFlags PluginM where
  getDynFlags = liftCoreM getDynFlags

getModGuts :: PluginM ModGuts
getModGuts = PluginM $ ReaderT (return . pluginModGuts)

-- TODO: Make this better by making PluginM an actual new type that
-- supports failure.
instance MonadCatch PluginM where
  catchM m _ = m

instance LiftCoreM PluginM where
  liftCoreM = PluginM . ReaderT . const

-- | For easier debugging
quickPrint :: (HasDynFlags m, MonadIO m, Outputable a) => a -> m ()
quickPrint a = do
  dynFlags <- getDynFlags
  liftIO $ print (runSDoc (ppr a) (initSDocContext dynFlags cmdlineParserStyle))

quickShow :: (HasDynFlags m, MonadIO m, Outputable a) => a -> m String
quickShow a = do
  dynFlags <- getDynFlags
  return . show $ runSDoc (ppr a) (initSDocContext dynFlags cmdlineParserStyle)

plugin :: Plugin
plugin = defaultPlugin
  { installCoreToDos = install
  }

install :: [CommandLineOption] -> [CoreToDo] -> CoreM [CoreToDo]
install _ todo = do
  reinitializeGlobals
  putMsgS "*** Accelerate transform plugin ***"
  return (todo ++ [CoreDoPluginPass "Accelerate transformation" (runPass pass)])

runPass :: (CoreProgram -> PluginM CoreProgram) -> ModGuts -> CoreM ModGuts
runPass p guts = bindsOnlyPass (\x -> (runReaderT (runPluginM $ p x) (PluginEnv guts))) guts

pass :: [CoreBind] -> PluginM [CoreBind]
pass = mapM (transformBind transformExpr)


transformBind :: Monad m => (Expr CoreBndr -> m (Expr CoreBndr)) -> Bind CoreBndr -> m (Bind CoreBndr)
transformBind f (NonRec b e) = do
  e' <- f e
  return $ NonRec b e'
transformBind f (Rec bs) = do
  e' <- mapM (traverse f) bs
  return $ Rec e'

infixl 0 :$
pattern (:$) :: Expr a -> Arg a -> Expr a
pattern f :$ x = App f x

infixl 0 <:$>
(<:$>) :: Functor f => Expr a -> f (Arg a) -> f (Expr a)
f <:$> x = fmap (App f) x

infixl 0 <:*>
(<:*>) :: Applicative f => f (Expr a) -> f (Arg a) -> f (Expr a)
f <:*> x = App <$> f <*> x

-- TODO: Put each kind of transformation into its own module.
transformExpr :: Expr CoreBndr -> PluginM (Expr CoreBndr)
transformExpr = return -- TODO: Implement

thLookupId :: TH.Name -> PluginM Id
thLookupId thName = do
  Just name <- liftCoreM (thNameToGhcName thName)
  lookupId name

thLookupTyCon :: TH.Name -> PluginM TyCon
thLookupTyCon thName = do
  Just name <- liftCoreM (thNameToGhcName thName)
  lookupTyCon name

-- TODO: Make a more robust solution
lookupAlt :: Bool -> [Alt CoreBndr] -> Expr CoreBndr
lookupAlt False [(_, _, a), _] = a
lookupAlt True  [_, (_, _, b)] = b
lookupAlt _ _ = error "lookupAlt: No match"

-- Adapted from HERMIT.Monad
runTcM :: TcM a -> PluginM a
runTcM m = do
    env <- getHscEnv'
    dflags <- getDynFlags
    guts <- getModGuts
    -- What is the effect of HsSrcFile (should we be using something else?)
    -- What should the boolean flag be set to?
    (msgs, mr) <- liftIO $ initTcFromModGuts env guts HsSrcFile False m
    let showMsgs (warns, errs) = showSDoc dflags $ vcat
                                                 $    text "Errors:" : pprErrMsgBagWithLoc errs
                                                   ++ text "Warnings:" : pprErrMsgBagWithLoc warns
    maybe (fail $ showMsgs msgs) return mr

buildDictionary :: Id -> PluginM (Id, [CoreBind])
buildDictionary evar = do
    runTcM $ do
#if __GLASGOW_HASKELL__ > 710
        loc <- getCtLocM (GivenOrigin UnkSkol) Nothing
#else
        loc <- getCtLoc $ GivenOrigin UnkSkol
#endif
        let predTy = varType evar
#if __GLASGOW_HASKELL__ > 710
            nonC = mkNonCanonical $ CtWanted { ctev_pred = predTy, ctev_dest = EvVarDest evar, ctev_loc = loc }
            wCs = mkSimpleWC [cc_ev nonC]
        -- TODO: Make sure solveWanteds is the right function to call.
        (_wCs', bnds) <- second evBindMapBinds <$> runTcS (solveWanteds wCs)
#else
            nonC = mkNonCanonical $ CtWanted { ctev_pred = predTy, ctev_evar = evar, ctev_loc = loc }
            wCs = mkSimpleWC [nonC]
        (_wCs', bnds) <- solveWantedsTcM wCs
#endif
        -- reportAllUnsolved _wCs' -- this is causing a panic with dictionary instantiation
                                  -- revist and fix!
        bnds1 <- initDsTc $ dsEvBinds bnds
        return (evar, bnds1)

buildDictionaryT :: Transform c PluginM Type CoreExpr
buildDictionaryT = prefixFailMsg "buildDictionaryT failed: " $ contextfreeT $ \ ty -> do
    dflags <- getDynFlags
    binder <- newIdH ("$d" ++ zEncodeString (filter (not . isSpace) (showPpr dflags ty))) ty
    (i,bnds) <- buildDictionary binder
    guardMsg (notNull bnds) "no dictionary bindings generated."
    return $ case bnds of
                [NonRec v e] | i == v -> e -- the common case that we would have gotten a single non-recursive let
                _ -> mkCoreLets bnds (varToCoreExpr i)

