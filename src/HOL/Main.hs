module HOL.Main where

import HOL.Ast
import HOL.TermNode

preludeSrc :: String
preludeSrc = unlines
    [ "module std.prelude."
    , ""
    ]
