{-# LANGUAGE DeriveFunctor #-}
module Hol.Front.Ast where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Z.Utils

type SmallId = String

type LargeId = String

type SymbolId = String

type Keyword = String

type IVar = Unique

type MTVar = Unique

type SrcPos = (Int, Int)

data Color
    = Black
    | Red
    | Blue
    deriving (Eq, Ord, Show)

data SrcLoc
    = SrcLoc { locLeft :: SrcPos, locRight :: SrcPos }
    deriving (Eq, Ord, Show)

data SymbolRep a
    = Prefix Prec a SymbolId
    | InfixL Prec a SymbolId a
    | InfixR Prec a SymbolId a
    | InfixO Prec a SymbolId a
    deriving (Eq, Ord, Show, Functor)

data Identifier
    = SmallId SmallId
    | LargeId LargeId
    | SymbolId SymbolId
    deriving (Eq, Ord, Show)

data TermExpr dcon annot
    = Var annot IVar
    | Con annot dcon
    | App annot (TermExpr dcon annot) (TermExpr dcon annot)
    | Lam annot IVar (TermExpr dcon annot)
    deriving (Eq, Ord, Show, Functor)

data ErrMsgBox
    = ErrMsgBox
        { boxSrcLoc :: SrcLoc
        , boxErrMsg :: [(Color, String)]
        }
    deriving (Eq, Ord, Show)

newtype Unique
    = Unique { unUnique :: Integer }
    deriving (Eq, Ord, Show)

getSymbolPrec :: SymbolRep a -> Prec
getSymbolPrec (Prefix prec _ _) = prec
getSymbolPrec (InfixL prec _ _ _) = prec
getSymbolPrec (InfixR prec _ _ _) = prec
getSymbolPrec (InfixO prec _ _ _) = prec

instance Semigroup SrcLoc where
    SrcLoc pos1 pos2 <> SrcLoc pos1' pos2' = SrcLoc (min pos1 pos1') (max pos2 pos2')

instance Outputable SrcLoc where
    pprint _ (SrcLoc { locLeft = (r1, c1), locRight = (r2, c2) }) = shows r1 . strstr ":" . shows c1 . strstr "-" . shows r2 . strstr ":" . shows c2
