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
pass = mapM transformBind


transformBind :: Bind CoreBndr -> CoreM (Bind CoreBndr)
transformBind (NonRec b e) = do
  e' <- transformExpr e
  return $ NonRec b e'
transformBind (Rec bs) = do
  e' <- mapM (traverse transformExpr) bs
  return $ Rec e'

infixl 0 :$
pattern f :$ x = App f x

transformExpr :: Expr CoreBndr -> CoreM (Expr CoreBndr)
transformExpr = transformRecs <=< transformBools

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
transformBools :: Expr CoreBndr -> CoreM (Expr CoreBndr)
transformBools e@(Var v)             = do
  repls <- boolReplacements
  case lookup (varName v) repls of
    Just repl -> return . Var $ setVarName v repl
    Nothing -> return e
transformBools e@(Lit {})            = return e
transformBools (App f x)             = App <$> transformBools f <*> transformBools x
transformBools (Lam v b)             = Lam v <$> transformBools b
transformBools (Let bnd b)           = Let <$> transformBind bnd <*> transformBools b
transformBools (Case e wild ty alts) =
  Case <$> transformBools e
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

