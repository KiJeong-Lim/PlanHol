module HOL.Front.Ast where

import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.State.Strict
import Control.Monad.Trans.Reader
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Z.Utils

type SmallId = String

type LargeId = String

type SPos = (Int, Int)

type MetaTVar = Unique

data SLoc
    = SLoc { _BegPos :: SPos, _EndPos :: SPos }
    deriving (Eq, Ord, Show)

data Literal
    = IntL Integer
    | ChrL Char
    | StrL String
    deriving (Eq, Ord)

data ModuleQual
    = NoQual
    | Qualed [SmallId] SmallId
    deriving (Eq, Ord, Show)

data Name
    = QualifiedName (ModuleQual) (SmallId)
    | UniquelyGened (Unique) (String)
    deriving (Eq, Ord, Show)

data CoreTerm var atom annot
    = CtVar (annot) (var)
    | CtCon (annot) (atom)
    | CtApp (annot) (CoreTerm var atom annot) (CoreTerm var atom annot)
    | CtLam (annot) (var) (CoreTerm var atom annot)
    deriving (Eq, Ord, Show, Functor)

data KindExpr
    = Star
    | KArr !(KindExpr) !(KindExpr)
    deriving (Eq, Ord, Show)

data TypeCtor
    = TypeCtor { nameOfTypeCtor :: Name, kindOfTypeCtor :: !(KindExpr) }
    deriving (Eq, Ord, Show)

data MonoType tvar
    = TyVar (tvar)
    | TyCon (TypeCtor)
    | TyApp (MonoType tvar) (MonoType tvar)
    | TyMTV (MetaTVar)
    deriving (Eq, Ord, Show, Functor)

data PolyType
    = Forall [SmallId] (MonoType Int)
    deriving (Eq, Ord, Show)

data Fixity annot
    = Prefix annot Prec
    | PrefixR annot Prec
    | Infix annot Prec annot
    | InfixL annot Prec annot
    | InfixR annot Prec annot
    | Suffix Prec annot
    | SuffixL Prec annot
    deriving (Eq, Ord, Show, Functor)

data Program rule
    = Program
        { nameOfModule :: ModuleQual
        , getFixityEnv :: Map.Map Name (Fixity ())
        , getMacroDefs :: Map.Map Name String
        , getKindDecls :: Map.Map Name KindExpr
        , getTypeDecls :: Map.Map Name PolyType
        , getRuleDecls :: [rule]
        }
    deriving (Eq, Ord, Show, Functor)

mapCtVar :: (var -> var') -> (CoreTerm var atom annot -> CoreTerm var' atom annot)
mapCtVar f (CtVar annot v) = CtVar annot $! f v
mapCtVar f (CtCon annot c) = CtCon annot c
mapCtVar f (CtApp annot t1 t2) = (CtApp annot $! mapCtVar f t1) $! mapCtVar f t2
mapCtVar f (CtLam annot v t1) = (CtLam annot $! f v) $! mapCtVar f t1

mapCtCon :: (atom -> atom') -> (CoreTerm var atom annot -> CoreTerm var atom' annot)
mapCtCon f (CtVar annot v) = CtVar annot v
mapCtCon f (CtCon annot c) = CtCon annot $! f c
mapCtCon f (CtApp annot t1 t2) = (CtApp annot $! mapCtCon f t1) $! mapCtCon f t2
mapCtCon f (CtLam annot v t1) = CtLam annot v $! mapCtCon f t1

readKind :: String -> KindExpr
readKind = go . loop 0 where
    go :: [(KindExpr, String)] -> KindExpr
    go [] = error "readKind: no parse..."
    go [(k, "")] = k
    go [_] = error "readKind: not EOF..."
    go _ = error "readKind: ambiguous parses..."
    loop :: Prec -> ReadS KindExpr
    loop 0 s = [ (KArr k1 k2, s'') | (k1, ' ' : '-' : '>' : ' ' : s') <- loop 1 s, (k2, s'') <- loop 0 s' ] ++ loop 1 s
    loop 1 ('*' : s) = [(Star, s)]
    loop 1 ('(' : s) = [ (k, s') | (k, ')' : s') <- loop 0 s ]
    loop _ _ = []

initialFixityEnv :: Map.Map Name (Fixity ())
initialFixityEnv = Map.fromList
    [ (QualifiedName preludeModule " -> ", InfixR () (negate 1) ())
    ]

preludeModule :: ModuleQual
preludeModule = Qualed [] "prim"

tyArrow :: TypeCtor
tyArrow = TypeCtor { nameOfTypeCtor = QualifiedName preludeModule " -> ", kindOfTypeCtor = readKind "* -> * -> *" }

tyO :: TypeCtor
tyO = TypeCtor { nameOfTypeCtor = QualifiedName preludeModule "o", kindOfTypeCtor = readKind "*" }

tyList :: TypeCtor
tyList = TypeCtor { nameOfTypeCtor = QualifiedName preludeModule "list", kindOfTypeCtor = readKind "* -> *" }

tyInt :: TypeCtor
tyInt = TypeCtor { nameOfTypeCtor = QualifiedName preludeModule "int", kindOfTypeCtor = readKind "*" }

tyChar :: TypeCtor
tyChar = TypeCtor { nameOfTypeCtor = QualifiedName preludeModule "char", kindOfTypeCtor = readKind "*" }

instance HasAnnot (CoreTerm var atom) where
    getAnnot (CtVar annot _) = annot
    getAnnot (CtCon annot _) = annot
    getAnnot (CtApp annot _ _) = annot
    getAnnot (CtLam annot _ _) = annot
    setAnnot annot (CtVar _ v) = CtVar annot v
    setAnnot annot (CtCon _ c) = CtCon annot c
    setAnnot annot (CtApp _ t1 t2) = CtApp annot t1 t2
    setAnnot annot (CtLam _ x t1) = CtLam annot x t1

instance Outputable KindExpr where
    pprint prec = dispatch where
        myPrecIs :: Int -> ShowS -> ShowS
        myPrecIs prec' ss = if prec > prec' then strstr "(" . ss . strstr ")" else ss
        dispatch :: KindExpr -> ShowS
        dispatch (Star) = myPrecIs 0 $ strstr "*"
        dispatch (KArr k1 k2) = myPrecIs 0 $ pprint 0 k1 . strstr " -> " . pprint 5 k2
