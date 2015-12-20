module Main where

import Types
import Log3
import Tests
import Data.Vector as V (Vector, (//), (!), empty)

main = chk 1 $ runp $ defp "[ x x A ] x A B"
