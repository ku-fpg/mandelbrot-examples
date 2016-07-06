{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TemplateHaskell #-}

module AccTransform (plugin) where

import           GhcPlugins

import           Data.Array.Accelerate hiding (map, (++))
import qualified Data.Array.Accelerate as A

import           Control.Monad

plugin :: Plugin
plugin = defaultPlugin
  { installCoreToDos = install
  }

install :: [CommandLineOption] -> [CoreToDo] -> CoreM [CoreToDo]
install _ todo = do
  reinitializeGlobals
  putMsgS "*** Accelerate transform plugin ***"
  return (todo ++ [CoreDoPluginPass "Accelerate transformation" (bindsOnlyPass pass)])

pass :: [CoreBind] -> CoreM [CoreBind]
pass = mapM (transformBind transformExpr)


transformBind :: (Expr CoreBndr -> CoreM (Expr CoreBndr)) -> Bind CoreBndr -> CoreM (Bind CoreBndr)
transformBind f (NonRec b e) = do
  e' <- f e
  return $ NonRec b e'
transformBind f (Rec bs) = do
  e' <- mapM (traverse f) bs
  return $ Rec e'

infixl 0 :$
pattern (:$) :: Expr a -> Arg a -> Expr a
pattern f :$ x = App f x

transformExpr :: Expr CoreBndr -> CoreM (Expr CoreBndr)
transformExpr = transformRecs <=< transformBools2 <=< transformBools

transformRecs :: Expr CoreBndr -> CoreM (Expr CoreBndr)
transformRecs = return

-- | Look for >, >=, etc and replace with >*, >=*, etc
boolReplacements :: CoreM [(Name, Name)]
boolReplacements =
  mapM (\(mx, my) -> do
          Just x <- thNameToGhcName mx
          Just y <- thNameToGhcName my
          return (x, y))
  [('(>=), '(>=*))
  ,('(<=), '(<=*))
  ,('(>),  '(>*))
  ,('(<),  '(A.<*))
  ]

-- TODO: Only replace boolean expressions of the appropriate type

applyBoolTransform :: Expr CoreBndr -> CoreM (Maybe (Expr CoreBndr))
applyBoolTransform e@(Var v) = do
  repls <- boolReplacements
  case lookup (varName v) repls of
    Just repl -> do
      return . Just . Var
             $ setVarName v repl
    Nothing -> return Nothing
applyBoolTransform _ = return Nothing

transformBools :: Expr CoreBndr -> CoreM (Expr CoreBndr)
transformBools e@(Var v)             = return e
transformBools e@(Lit {})            = return e
transformBools e@(f :$ Type ty1 :$ dict :$ x :$ y) = do
  fm' <- applyBoolTransform f
  case fm' of
    Just f' ->
      return (f' :$ Type ty1 :$ x :$ y)
    Nothing ->
      return e
transformBools (App f x)             = App <$> transformBools f <*> transformBools x
transformBools (Lam v b)             = Lam v <$> transformBools b
transformBools (Let bnd b)           = Let <$> transformBind transformBools bnd <*> transformBools b
transformBools (Case c wild ty alts) =
  Case <$> transformBools c
       <*> pure wild
       <*> pure ty
       <*> mapM (\(x, y, z) -> do
                     z' <- transformBools z
                     return (x, y, z'))
                alts
transformBools (Cast e co)           = Cast <$> transformBools e <*> pure co
transformBools (Tick t e)            = Tick t <$> transformBools e
transformBools e@(Type {})           = return e
transformBools e@(Coercion {})       = return e

-- | Second boolean transformation pass. Turn cases into 'cond's
transformBools2 :: Expr CoreBndr -> CoreM (Expr CoreBndr)
transformBools2 e@(Var {})            = return e
transformBools2 e@(Lit {})            = return e
transformBools2 (App f x)             = App <$> transformBools2 f <*> transformBools2 x
transformBools2 (Lam v b)             = Lam v <$> transformBools2 b
transformBools2 (Let bnd b)           = Let <$> transformBind transformBools2 bnd <*> transformBools2 b
transformBools2 e@(Case c wild ty alts) = do
  b <- isAccBool c
  if b
    then undefined
    else return e
transformBools2 (Cast e co)           = Cast <$> transformBools2 e <*> pure co
transformBools2 (Tick t e)            = Tick t <$> transformBools2 e
transformBools2 e@(Type {})           = return e
transformBools2 e@(Coercion {})       = return e

isAccBool :: Expr CoreBndr -> CoreM Bool
isAccBool (Var f :$ x :$ y) = do
  repls <- fmap (map (\(a, b) -> (b, a))) boolReplacements
  case lookup (varName f) repls of
    Just _  -> error "Found!"
    Nothing -> return False
isAccBool _ = return False

