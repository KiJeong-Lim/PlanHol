module Hol.Front.Ast where

import Z.Utils

type SmallId = String

type LargeId = String

type SymbolId = String

type Keyword = String

type IVar = Unique

type MTVar = Unique

data SrcPos
    = SrcPos { posRow :: Int, posCol :: Int }
    deriving (Eq, Ord, Show)

data SrcLoc
    = SrcLoc { locLeft :: SrcPos, locRight :: SrcPos }
    deriving (Eq, Ord, Show)

data SymbolRep a
    = Prefix Prec a SymbolId
    | InfixL Prec a SymbolId a
    | InfixR Prec a SymbolId a
    | InfixO Prec a SymbolId a
    deriving (Eq, Ord, Show)

data Identifier
    = SmallId SmallId
    | LargeId LargeId
    | SymbolId (SymbolRep ())
    deriving (Eq, Ord, Show)

data TermExpr dcon annot
    = Var annot IVar
    | Con annot dcon 
    | App annot (TermExpr dcon annot) (TermExpr dcon annot)
    | Lam annot IVar (TermExpr dcon annot)
    deriving (Eq, Ord, Show)

newtype Unique
    = Unique { unUnique :: Integer }
    deriving (Eq, Ord, Show)

getSymbolPrec :: SymbolRep a -> Prec
getSymbolPrec (Prefix prec _ _) = prec
getSymbolPrec (InfixL prec _ _ _) = prec
getSymbolPrec (InfixR prec _ _ _) = prec
getSymbolPrec (InfixO prec _ _ _) = prec

instance Outputable SrcPos where
    pprint _ pos = shows (posRow pos) . strstr ":" . shows (posCol pos)

instance Outputable SrcLoc where
    pprint _ loc = pprint 0 (locLeft loc) . strstr "-" . pprint 0 (locRight loc)
