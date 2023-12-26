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
    | KwIf
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
    | KwClass
    | KwWhere
    | KwForall
    | KwExists
    | KwPrefix
    | KwInfixL
    | KwInfixR
    | KwInfixO
    deriving (Eq, Ord, Show)

data Token annot
    = TokKeyword annot TokKeyword
    | TokSmallId annot SmallId
    | TokLargeId annot LargeId
    | TokSymbolId annot SymbolId
    | TokNatLit annot Integer
    | TokChrLit annot Char
    | TokStrLit annot String
    deriving (Eq, Ord, Show)

data RawTerm annot
    = RVar annot Identifier
    | RCon annot DCon
    | RApp annot (RawTerm annot) (RawTerm annot)
    | RLam annot Identifier (RawTerm annot)
    | RTermExtra annot (RawTerm annot) String
    deriving (Eq, Ord, Show)

data RawType annot
    = RTyVar annot Identifier
    | RTyCon annot DCon
    | RTyApp annot (RawType annot) (RawType annot)
    | RTypeExtra annot (RawType annot) String
    deriving (Eq, Ord, Show)

data RawKind annot
    = RKindStar annot
    | RKindArrow annot (RawKind annot) (RawKind annot)
    | RKindExtra annot (RawKind annot) String
    deriving (Eq, Ord, Show)

data CtorDecl
    = CtorDecl SrcLoc Identifier (RawTerm SrcLoc)
    deriving (Eq, Ord, Show)

data MethodDecl
    = MethodDecl SrcLoc (RawType SrcLoc)
    deriving (Eq, Ord, Show)

data TopLevelStmt
    = FactDefn SrcLoc (RawTerm SrcLoc)
    | DataDefn SrcLoc Identifier (RawKind SrcLoc) [CtorDecl]
    | TypeDefn SrcLoc Identifier (RawType SrcLoc)
    | TypeDecl SrcLoc Identifier (RawType SrcLoc)
    | ClassDecl SrcLoc Identifier (RawKind SrcLoc) [MethodDecl]
    | SymbolDecl SrcLoc (SymbolRep ())
    deriving (Eq, Ord, Show)

mkNatLit :: SrcLoc -> Integer -> RawTerm SrcLoc
mkNatLit loc n = RCon loc (DConNatL n)

mkChrLit :: SrcLoc -> Char -> RawTerm SrcLoc
mkChrLit loc ch = RCon loc (DConChrL ch)

mkStrLit :: SrcLoc -> String -> RawTerm SrcLoc
mkStrLit loc str = foldr (\ch -> \acc -> RApp loc (RApp loc (RCon loc DConCons) (RCon loc (DConChrL ch))) acc) (RCon loc DConNil) str

instance Outputable TokKeyword where
    pprint _ KwLParen = strstr "("
    pprint _ KwRParen = strstr ")"
    pprint _ KwLBracket = strstr "["
    pprint _ KwRBracket = strstr "]"
    pprint _ KwLBrace = strstr "{"
    pprint _ KwRBrace = strstr "}"
    pprint _ KwIf = strstr ":-"
    pprint _ KwDoubleColon = strstr "::"
    pprint _ KwComma = strstr ","
    pprint _ KwColon = strstr ":"
    pprint _ KwSemicolon = strstr ";"
    pprint _ KwDot = strstr "."
    pprint _ KwArrow = strstr "->"
    pprint _ KwBSlash = strstr "\\"
    pprint _ KwPercent = strstr "%"
    pprint _ KwEqual = strstr "="
    pprint _ KwData = strstr "data"
    pprint _ KwType = strstr "type"
    pprint _ KwClass = strstr "classs"
    pprint _ KwWhere = strstr "where"
    pprint _ KwForall = strstr "forall"
    pprint _ KwExists = strstr "exists"
    pprint _ KwPrefix = strstr "prefix"
    pprint _ KwInfixL = strstr "infixl"
    pprint _ KwInfixR = strstr "infixr"
    pprint _ KwInfixO = strstr "infix"

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

instance HasAnnot RawTerm where
    annot (RVar a _) = a
    annot (RCon a _) = a
    annot (RApp a _ _) = a
    annot (RLam a _ _) = a
    annot (RTermExtra a t1 _) = a

instance Functor RawTerm where
    fmap a2b (RVar a x) = RVar (a2b a) x
    fmap a2b (RCon a c) = RCon (a2b a) c
    fmap a2b (RApp a t1 t2) = RApp (a2b a) (fmap a2b t1) (fmap a2b t2)
    fmap a2b (RLam a x t1) = RLam (a2b a) x (fmap a2b t1)
    fmap a2b (RTermExtra a t1 extra) = RTermExtra (a2b a) (fmap a2b t1) extra

instance HasAnnot RawType where
    annot (RTyVar a _) = a
    annot (RTyCon a _) = a
    annot (RTyApp a _ _) = a
    annot (RTypeExtra a _ _) = a

instance Functor RawType where
    fmap a2b (RTyVar a x) = RTyVar (a2b a) x
    fmap a2b (RTyCon a c) = RTyCon (a2b a) c
    fmap a2b (RTyApp a t1 t2) = RTyApp (a2b a) (fmap a2b t1) (fmap a2b t2)
    fmap a2b (RTypeExtra a t1 extra) = RTypeExtra (a2b a) (fmap a2b t1) extra

instance HasAnnot RawKind where
    annot (RKindStar a) = a
    annot (RKindArrow a _ _) = a
    annot (RKindExtra a _ _) = a
