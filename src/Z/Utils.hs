module Z.Utils where

import Text.ParserCombinators.ReadP

type ErrMsg = String

type Prec = Int

class Outputable a where
    pprint :: Prec -> a -> ShowS

class EquivRel a where
    infix 4 `equiv`
    equiv :: a -> a -> Bool

class EquivRel a => Preorder a where
    infix 4 =<
    (=<) :: a -> a -> Bool

class HasAnnot f where
    annot :: f a -> a

strstr :: String -> ShowS
strstr = (++)
{-# INLINABLE strstr #-}

strcat :: [ShowS] -> ShowS
strcat = foldr (.) id
{-# INLINABLE strcat #-}

pshow :: Outputable a => a -> String
pshow x = pprint 0 x ""
