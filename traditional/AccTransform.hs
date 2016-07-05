{-# LANGUAGE PatternSynonyms #-}

module AccTransform (plugin) where

import           GhcPlugins

plugin :: Plugin
plugin = defaultPlugin
  { installCoreToDos = install
  }

install :: [CommandLineOption] -> [CoreToDo] -> CoreM [CoreToDo]
install _ todo = do
  reinitializeGlobals
  putMsgS "Hello!"
  return (CoreDoPluginPass "Accelerate transformation" (bindsOnlyPass pass) : todo)

pass :: [CoreBind] -> CoreM [CoreBind]
pass = mapM go
  where
    go (NonRec b e) =
      return $ NonRec b (transformExpr e)
    go (Rec bs) =
      return . Rec $ map (fmap transformExpr) bs

infixl 0 :$
pattern f :$ x = App f x

transformExpr :: Expr CoreBndr -> Expr CoreBndr
transformExpr e@(Var _ :$ f :$ w :$ h) = error "Transform stub"

