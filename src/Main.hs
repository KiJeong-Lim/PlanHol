module Main where

import qualified ALPHA1.Main as ALPHA1
import qualified ALPHA2.Main as ALPHA2
import qualified LGS.Main as LGS
import qualified PGS.Main as PGS
import System.Console.Pretty
import Z.Utils

main :: IO ()
main = do
    prettyable <- supportsPretty
    putStr "colorable="
    print prettyable
    ALPHA2.main
