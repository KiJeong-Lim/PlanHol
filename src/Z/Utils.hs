module Z.Utils where

import Text.ParserCombinators.ReadP

type ErrMsg = String

type Prec = Int

class Outputable a where
    pprint :: Prec -> a -> ShowS

class EquivRel a where
    infix 4 `equiv`
    equiv :: a -> a -> Bool

class Preorder a where
    infix 4 =<
    (=<) :: a -> a -> Bool

strstr :: String -> ShowS
strstr = (++)
{-# INLINABLE strstr #-}

strcat :: [ShowS] -> ShowS
strcat = foldr (.) id
{-# INLINABLE strcat #-}
