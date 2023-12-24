module Z.Utils where

import Text.ParserCombinators.ReadP

infix 4 `equiv`

type ErrMsg = String

type Prec = Int

class Outputable a where
    pprint :: Prec -> a -> ShowS

class EquivRel a where
    equiv :: a -> a -> Bool

strstr :: String -> ShowS
strstr = (++)
{-# INLINABLE strstr #-}
