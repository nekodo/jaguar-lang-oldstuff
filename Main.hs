module Main where

import Tiger
--import Jungle
import Yesod

main = do
  --warpDebug 3000 W
  op <- loadModule "test.tg"
  prettyPutStrLn op