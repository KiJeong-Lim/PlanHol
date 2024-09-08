module ALPHA1.Main where

import ALPHA1.Ast
import ALPHA1.TermNode

preludeSrc :: String
preludeSrc = unlines
    [ "module std.prelude."
    , ""
    ]
