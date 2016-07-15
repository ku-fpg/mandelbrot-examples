{-# LANGUAGE PatternSynonyms #-} {-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module AccTransform (plugin) where

import           GhcPlugins hiding (($$))

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

import           Control.Arrow (second)
import           Data.Char (isSpace)

import           ErrUtils
import           Pair
import           Class

import           Control.Monad.Reader

import qualified Language.Haskell.TH.Syntax as TH

newtype PluginM a = PluginM { runPluginM :: ReaderT ModGuts CoreM a }
    deriving (Functor, Applicative, Monad
             ,MonadIO, MonadReader ModGuts)

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
getModGuts = PluginM $ ReaderT return

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
runPass p guts = bindsOnlyPass (\x -> (runReaderT (runPluginM $ p x) guts)) guts

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

infixl 0 $$
($$) :: Functor f => Expr a -> f (Arg a) -> f (Expr a)
f $$ x = fmap (App f) x

infixl 0 $*
($*) :: Applicative f => f (Expr a) -> f (Arg a) -> f (Expr a)
f $* x = App <$> f <*> x

transformExpr :: Expr CoreBndr -> PluginM (Expr CoreBndr)
transformExpr = transformRecs <=< transformBools2 <=< transformBools

-- | Apply a transformation top-down
applyTransformTD :: Applicative f =>
  (Expr CoreBndr -> Maybe ((a -> f a) -> f (Expr CoreBndr))) ->
  (a -> f a) ->
  Expr CoreBndr ->
  f (Expr CoreBndr)
applyTransformTD c t e =
  case c e of
    Nothing ->
      case e of
        Var {} -> pure e
        Lit {} -> pure e
        App f x -> App <$> applyTransformTD c t f <*> applyTransformTD c t x
        Lam b e -> Lam b <$> applyTransformTD c t e
        Let (NonRec b e) e' -> Let <$> (NonRec b <$> applyTransformTD c t e)
                                   <*> applyTransformTD c t e'
        Let (Rec bnds) e    -> Let <$> (Rec <$> (traverse (\ (x, y) -> (x,) <$> applyTransformTD c t y) bnds))
                                   <*> applyTransformTD c t e
        Case s wild ty alts -> Case <$> applyTransformTD c t s
                                    <*> pure wild
                                    <*> pure ty
                                    <*> traverse (\ (x, y, z) -> (x, y,) <$> applyTransformTD c t z) alts
        Cast e' coercion -> Cast <$> applyTransformTD c t e' <*> pure coercion
        Tick i e'   -> Tick i <$> applyTransformTD c t e'
        Type {}     -> pure e
        Coercion {} -> pure e

    Just f -> f t


-- | Transform a recursive 'go' in 'generate ... go' to a non-recursive go.
transformRecs :: Expr CoreBndr -> PluginM (Expr CoreBndr)
transformRecs = return

-- | Look for >, >=, etc and replace with >*, >=*, etc
boolReplacements :: CoreM [(Name, Name)]
boolReplacements =
  mapM (\(mx, my) -> do
          Just x <- thNameToGhcName mx
          Just y <- thNameToGhcName my
          return (x, y))
  [('(>=), '(A.>=*))
  ,('(<=), '(A.<=*))
  ,('(>),  '(A.>*))
  ,('(<),  '(A.<*))
  ,('(==), '(A.==*))
  ,('(/=), '(A./=*))
  ,('(||), '(A.||*))
  ,('(&&), '(A.&&*))
  ]

-- TODO: Only replace boolean expressions of the appropriate type
applyBoolTransform :: Expr CoreBndr -> PluginM (Maybe (Expr CoreBndr))
applyBoolTransform e@(Var v) = do
  repls <- liftCoreM boolReplacements
  case lookup (varName v) repls of
    Just repl -> do
      replId <- lookupId repl
      return . Just
             $ Var replId
    Nothing -> return Nothing
applyBoolTransform _ = return Nothing

transformBools :: Expr CoreBndr -> PluginM (Expr CoreBndr)
transformBools e@(Var {})            = return e
transformBools e@(Lit {})            = return e
transformBools e@(_f :$ Type _ty1 :$ Var _dict :$ _x :$ _y) = do
  me' <- transformBoolExpr e
  case me' of
    Just e' -> return e'
    Nothing -> return e
transformBools (App f x)             = App <$> transformBools f <*> transformBools x
transformBools (Lam v b)             = Lam v <$> transformBools b
transformBools (Let bnd b)           = Let <$> transformBind transformBools bnd <*> transformBools b
transformBools (Case c wild ty alts) = do
    -- We do this for Case so we can change the type appropriately.
  mc' <- transformBoolExpr c
  alts' <- mapM (\(x, y, z) -> do
                     z' <- transformBools z
                     return (x, y, z'))
                alts

  Case <$> transformBools c
       <*> pure wild
       <*> pure ty
       <*> pure alts'
transformBools (Cast e co)           = Cast <$> transformBools e <*> pure co
transformBools (Tick t e)            = Tick t <$> transformBools e
transformBools e@(Type {})           = return e
transformBools e@(Coercion {})       = return e

transformBoolExpr :: Expr CoreBndr -> PluginM (Maybe (Expr CoreBndr))
transformBoolExpr e@(f :$ Type ty1 :$ Var dict :$ x :$ y) = do
  fm' <- applyBoolTransform f
  case fm' of
    Just f' -> do
      Just eltName <- liftCoreM (thNameToGhcName ''Elt)
      eltTyCon <- lookupTyCon eltName

      Just isScalarName <- liftCoreM (thNameToGhcName ''IsScalar)
      isScalarTyCon <- lookupTyCon isScalarName

      let Just [ty1'] = tyConAppArgs_maybe ty1

      eltDict <- applyT buildDictionaryT () (mkTyConApp eltTyCon [ty1'])
      isScalarDict <- applyT buildDictionaryT () (mkTyConApp isScalarTyCon [ty1'])

      return $ Just (f' :$ Type ty1' :$ eltDict :$ isScalarDict :$ x :$ y)
    Nothing -> return Nothing
transformBoolExpr _ = return Nothing

-- | Second boolean transformation pass. Turn cases into 'cond's
-- TODO: Base the Case check on the scrutinee type instead of the scrutinee
-- value.
transformBools2 :: Expr CoreBndr -> PluginM (Expr CoreBndr)
transformBools2 e@(Var {})            = return e
transformBools2 e@(Lit {})            = return e
transformBools2 (App f x)             = App <$> transformBools2 f <*> transformBools2 x
transformBools2 (Lam v b)             = Lam v <$> transformBools2 b
transformBools2 (Let bnd b)           = Let <$> transformBind transformBools2 bnd <*> transformBools2 b
transformBools2 e@(Case c wild ty alts) = do
  b <- isAccBool c

  case b of
    Just v -> do
      condId       <- thLookupId 'cond
      liftId       <- thLookupId 'A.lift
      eltTyCon     <- thLookupTyCon ''Elt
      plainTyCon   <- thLookupTyCon ''Plain
      expTyCon     <- thLookupTyCon ''Exp
      liftClsTyCon <- thLookupTyCon ''A.Lift

      instEnvs <- runTcM tcGetFamInstEnvs

          -- This is "Plain <ty>"
      let ty'           = mkTyConApp plainTyCon [ty]

          -- This should be ty with the Exps removed.
      let normalisedTy' = snd $ normaliseType instEnvs Representational ty'

      dictV <- applyT buildDictionaryT () (mkTyConApp eltTyCon [normalisedTy'])

          -- Here, the 'snd' gets the actual normalised type out.
      let normalisedTy = snd $ normaliseType instEnvs Representational ty

      liftDict <- applyT buildDictionaryT () (mkTyConApp liftClsTyCon [mkTyConTy expTyCon, normalisedTy])

          -- Bring Exp outside. For example "(Exp Float, Exp Float, Exp Float)"
          -- becomes "Exp (Float, Float, Float)" by way of
          -- "Exp (Plain (Exp Float, Exp Float, Exp Float))"
      let castIt x = Cast x (fst (normaliseType instEnvs Representational (mkTyConApp expTyCon [ty'])))

      let liftIt :: PluginM (Expr CoreBndr) -> PluginM (Expr CoreBndr)
          liftIt = fmap $ castIt . (Var liftId :$ Type (mkTyConTy expTyCon) :$ Type normalisedTy :$ liftDict :$)

      Var condId :$ Type normalisedTy' :$ dictV
                 :$ c
                 $$ liftIt (transformBools2 (lookupAlt False alts))
                 $* liftIt (transformBools2 (lookupAlt True  alts))

    Nothing ->
      Case <$> transformBools2 c
           <*> pure wild
           <*> pure ty
           <*> mapM (\(x, y, z) -> do
                         z' <- transformBools2 z
                         return (x, y, z'))
                    alts
transformBools2 (Cast e co)           = Cast <$> transformBools2 e <*> pure co
transformBools2 (Tick t e)            = Tick t <$> transformBools2 e
transformBools2 e@(Type {})           = return e
transformBools2 e@(Coercion {})       = return e

thLookupId :: TH.Name -> PluginM Id
thLookupId thName = do
  Just name <- liftCoreM (thNameToGhcName thName)
  lookupId name

thLookupTyCon :: TH.Name -> PluginM TyCon
thLookupTyCon thName = do
  Just name <- liftCoreM (thNameToGhcName thName)
  lookupTyCon name

isAccBool :: Expr CoreBndr -> PluginM (Maybe (Expr CoreBndr))
isAccBool (v@(Var f) :$ Type _ty :$ _dict1 :$ _dict2 :$ _ :$ _) = do
  repls <- fmap (map (\(a, b) -> (b, a))) $ liftCoreM boolReplacements
  case lookup (varName f) repls of
    Just _  -> return $ Just v
    Nothing -> return Nothing
isAccBool _ = return Nothing

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
    guts <- ask
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

