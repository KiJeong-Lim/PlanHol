{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Redundant bracket" #-}
{-# LANGUAGE DeriveFunctor #-}
module Hol.BEnd.Term where

import Hol.BEnd.Unique

type DbIdx = Int

type Name = String

data Term v c a
    = LVar (v)
    | NIdx (DbIdx)
    | NCon (c)
    | NApp (Term v c a) (Term v c a)
    | NLam (Term v c a)
    | NAnn a (Term v c a)
    deriving (Eq, Ord, Show, Functor)
