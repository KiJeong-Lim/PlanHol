module Hol.Front.Grammar where

import Hol.Front.Ast
import Z.Utils

data TokKeyword
    = KwLParen
    | KwRParen
    | KwLBracket
    | KwRBracket
    | KwLBrace
    | KwRBrace
    | KwDoubleColon
    | KwComma
    | KwColon
    | KwSemicolon
    | KwDot
    | KwArrow
    | KwBSlash
    | KwPercent
    | KwEqual
    | KwData
    | KwType
    deriving (Eq, Ord, Show)

instance Outputable TokKeyword where
    pprint _ KwLParen = strstr "("
    pprint _ KwRParen = strstr ")"
    pprint _ KwLBracket = strstr "["
    pprint _ KwRBracket = strstr "]"
    pprint _ KwLBrace = strstr "{"
    pprint _ KwRBrace = strstr "}"
    pprint _ KwDoubleColon = strstr "::"
    pprint _ KwComma = strstr ","
    pprint _ KwColon = strstr ":"
    pprint _ KwSemicolon = strstr ";"
    pprint _ KwDot = strstr "."
    pprint _ KwBSlash = strstr "\\"
    pprint _ KwPercent = strstr "%"
    pprint _ KwEqual = strstr "="
    pprint _ KwData = strstr "data"
    pprint _ KwType = strstr "type"

data Token annot
    = TokKeyword annot TokKeyword
    | TokSmallId annot SmallId
    | TokLargeId annot LargeId
    | TokSymbolId annot SymbolId
    | TokNatLit annot Integer
    | TokChrLit annot Char
    | TokStrLit annot String
    deriving (Eq, Ord, Show)

instance HasAnnot Token where
    annot (TokKeyword a _) = a
    annot (TokSmallId a _) = a
    annot (TokLargeId a _) = a
    annot (TokSymbolId a _) = a
    annot (TokNatLit a _) = a
    annot (TokChrLit a _) = a
    annot (TokStrLit a _) = a

instance Functor Token where
    fmap a2b (TokKeyword a kwrd) = TokKeyword (a2b a) kwrd
    fmap a2b (TokSmallId a sid) = TokSmallId (a2b a) sid
    fmap a2b (TokLargeId a lid) = TokLargeId (a2b a) lid
    fmap a2b (TokSymbolId a sym) = TokSymbolId (a2b a) sym
    fmap a2b (TokNatLit a n) = TokNatLit (a2b a) n
    fmap a2b (TokChrLit a ch) = TokChrLit (a2b a) ch
    fmap a2b (TokStrLit a str) = TokStrLit (a2b a) str
