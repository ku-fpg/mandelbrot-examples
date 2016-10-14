module AccTransformScript where

import           Prelude hiding (repeat)

import           HERMIT.API
import           HERMIT.API.Types

fullBetaReduce :: Rewrite LCore
fullBetaReduce = betaReduce >>> letSubst

script :: Shell ()
script = do
  setPath $ rhsOf "main"
  apply . oneTD $ unfoldRuleUnsafe "abs-intro"

  apply . oneTD $ unfoldWith "inline"
  apply . oneTD $ unfoldWith "pointColor"

  mapM_ (apply . repeat . oneTD . unfoldRuleUnsafe)
        [ ">=*-intro"
        , "+-intro"
        , "*-intro"
        , "--intro"
        ]

  apply . repeat $ oneTD caseFloat
  apply . repeat $ oneTD letFloatCase

  apply $ repeat (extractR $ focus (applicationOf "abs")
                                   (promote (caseFloatArgLemma "abs-lemma" <+ letFloat)))

  proofCmd assume

  apply smash

  -- Recursion --
  apply $ oneTD fixIntro
  apply $ oneTD letSubst -- See if this can be combined into the above line so
                         -- correct let is always substituted.

  apply . oneTD $ unfoldRuleUnsafe "fix-abs-rep-intro"
  apply . repeat . oneTD $ fullBetaReduce

  apply $ extractR $ focus (applicationOf "abs")
                           (promote (caseFloatArgLemma "abs-lemma" <+ letFloat))
  proofCmd assume


  -- apply . oneTD $ unfoldRuleUnsafe "abs-if->cond"

