module HOL.Front.Ast where

import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.State.Strict
import Data.Char
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Z.Algo.Function
import Z.Utils

type SmallId = String

type LargeId = String

type SPos = (Int, Int)

type MetaTVar = Unique

type MacroDef = (List String, String)

data SLoc
    = SLoc { _BegPos :: SPos, _EndPos :: SPos }
    deriving (Eq, Ord, Show)

data Literal
    = IntL (Integer)
    | ChrL (Char)
    | StrL (String)
    deriving (Eq, Ord)

data ModuleQual
    = NoQual
    | Qualed (List SmallId, SmallId)
    deriving (Eq, Ord, Show)

data Name
    = QualifiedName (ModuleQual) (SmallId)
    | UniquelyGened (Unique) (String)
    deriving (Eq, Ord, Show)

data LVar
    = LVarNamed (LargeId)
    | LVarUnique (Unique)
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
    = TyVar !(tvar)
    | TyCon !(TypeCtor)
    | TyApp !(MonoType tvar) !(MonoType tvar)
    | TyMTV !(MetaTVar)
    deriving (Eq, Ord, Show, Functor)

data PolyType
    = Forall (List LargeId) (MonoType Int)
    deriving (Eq, Ord, Show)

data Fixity annot
    = Prefix (annot) (Prec)
    | PrefixR (annot) (Prec)
    | Infix (annot) (Prec) (annot)
    | InfixL (annot) (Prec) (annot)
    | InfixR (annot) (Prec) (annot)
    | Suffix (Prec) (annot)
    | SuffixL (Prec) (annot)
    deriving (Eq, Ord, Show, Functor)

data Program rule
    = Program
        { nameOfModule :: ModuleQual
        , importModule :: List ModuleQual
        , getFixityEnv :: Map.Map Name (Fixity ())
        , getMacroDefs :: Map.Map Name (List String, String)
        , getKindDecls :: Map.Map Name KindExpr
        , getTypeDecls :: Map.Map Name PolyType
        , getRuleDecls :: List rule
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
    loop 0 s = [ (KArr k1 k2, s'') | (k1, ' ' : '-' : '>' : ' ' : s') <- loop 1 s, (k2, s'') <- loop 0 s' ] /> loop 1 s
    loop 1 ('*' : s) = one (Star, s)
    loop 1 ('(' : s) = [ (k, s') | (k, ')' : s') <- loop 0 s ]
    loop _ _ = []

preludeModule :: ModuleQual
preludeModule = Qualed (["std", "__primitive"], "prelude")

tyArrow :: TypeCtor
tyArrow = TypeCtor { nameOfTypeCtor = QualifiedName preludeModule " -> ", kindOfTypeCtor = readKind "* -> * -> *" }

tyO :: TypeCtor
tyO = TypeCtor { nameOfTypeCtor = QualifiedName preludeModule "o", kindOfTypeCtor = readKind "*" }

tyList :: TypeCtor
tyList = TypeCtor { nameOfTypeCtor = QualifiedName preludeModule "list", kindOfTypeCtor = readKind "* -> *" }

tyNat :: TypeCtor
tyNat = TypeCtor { nameOfTypeCtor = QualifiedName preludeModule "nat", kindOfTypeCtor = readKind "*" }

tyChar :: TypeCtor
tyChar = TypeCtor { nameOfTypeCtor = QualifiedName preludeModule "char", kindOfTypeCtor = readKind "*" }

mkTyArrow :: MonoType a -> MonoType a -> MonoType a
ty1 `mkTyArrow` ty2 = TyApp (TyApp (TyCon tyArrow) ty1) ty2

mkTyO :: MonoType Int
mkTyO = TyCon tyO

mkTyList :: MonoType Int -> MonoType Int
mkTyList ty1 = TyApp (TyCon tyList) ty1

mkTyNat :: MonoType Int
mkTyNat = TyCon tyNat

mkTyChar :: MonoType Int
mkTyChar = TyCon tyChar

readType :: String -> PolyType
readType = mkTy . readTypeExpr 0 where
    usual :: Char -> Bool
    usual c = isUpper c || isLower c || isDigit c || c == '_'
    readTyVar :: ReadS String
    readTyVar (c : s) = if c `elem` ['A' .. 'Z'] then one (c : takeWhile usual s, dropWhile usual s) else []
    readTyVar _ = []
    readTyCon :: ReadS String
    readTyCon (c : s) = if c `elem` ['a' .. 'z'] then one (c : takeWhile usual s, dropWhile usual s) else []
    readTyCon _ = []
    maximal :: ReadS a -> ReadS [a]
    maximal p s = [ (x : xs, s'') | (x, s') <- p s, (xs, s'') <- maximal p s' ] /> one ([], s)
    readSpace :: ReadS a -> ReadS a
    readSpace p (' ' : s) = p s
    readSpace _ _ = []
    readTypeExpr :: Prec -> ReadS (MonoType String)
    readTypeExpr 0 s = [ (mkTyArrow ty1 ty2, s'') | (ty1, ' ' : '-' : '>' : ' ' : s') <- readTypeExpr 1 s, (ty2, s'') <- readTypeExpr 0 s' ] /> readTypeExpr 1 s
    readTypeExpr 1 s = [ (List.foldl' TyApp ty tys, s'') | (ty, s') <- readTypeExpr 2 s, (tys, s'') <- maximal (readSpace (readTypeExpr 2)) s' ]
    readTypeExpr 2 s = [ (TyVar v, s') | (v, s') <- readTyVar s ] /> [ (mkTyCon tc, s') | (tc, s') <- readTyCon s ] /> readTypeExpr 3 s
    readTypeExpr _ ('(' : s) = [ (ty, s') | (ty, ')' : s') <- readTypeExpr 0 s ]
    readTypeExpr _ _ = []
    mkTyCon :: String -> MonoType String
    mkTyCon "o" = TyCon tyO
    mkTyCon "list" = TyCon tyList
    mkTyCon "nat" = TyCon tyNat
    mkTyCon "char" = TyCon tyChar
    collectTyVar :: MonoType String -> Set.Set String
    collectTyVar = flip go Set.empty where
        go :: MonoType String -> Set.Set String -> Set.Set String
        go (TyVar v) = Set.insert v
        go (TyCon c) = id
        go (TyApp ty1 ty2) = go ty1 . go ty2
        go (TyMTV x) = id
    mkTy :: [(MonoType String, String)] -> PolyType
    mkTy [] = error "readType: no parse..."
    mkTy [(ty, "")] = let tyvars = Set.toList (collectTyVar ty) in Forall tyvars (convert tyvars ty)
    mkTy [_] = error "readType: not EOF..."
    mkTy x = error "readType: ambiguous parses..."
    convert :: [String] -> MonoType String -> MonoType Int
    convert nms (TyVar v) = maybe (error "readType: unreachable...") TyVar (v `List.elemIndex` nms)
    convert nms (TyCon c) = TyCon c
    convert nms (TyApp ty1 ty2) = TyApp (convert nms ty1) (convert nms ty2)
    convert nms (TyMTV x) = TyMTV x 

preludeFixityEnv :: Map.Map Name (Fixity ())
preludeFixityEnv = Map.fromList
    [ (QualifiedName preludeModule " -> ", InfixR () (negate 1) ())
    , (QualifiedName preludeModule " :- ", InfixR () 0 ())
    , (QualifiedName preludeModule "; ", InfixR () 1 ())
    , (QualifiedName preludeModule ", ", InfixR () 2 ())
    , (QualifiedName preludeModule " => ", InfixR () 3 ())
    , (QualifiedName preludeModule " = ", Infix () 4 ())
    , (QualifiedName preludeModule " < ", Infix () 4 ())
    , (QualifiedName preludeModule " > ", Infix () 4 ())
    , (QualifiedName preludeModule " =< ", Infix () 4 ())
    , (QualifiedName preludeModule " >= ", Infix () 4 ())
    , (QualifiedName preludeModule " := ", Infix () 4 ())
    , (QualifiedName preludeModule " :: ", InfixR () 5 ())
    , (QualifiedName preludeModule " + ", InfixL () 6 ())
    , (QualifiedName preludeModule " - ", InfixL () 6 ())
    , (QualifiedName preludeModule " * ", InfixL () 7 ())
    , (QualifiedName preludeModule " / ", InfixL () 7 ())
    , (QualifiedName preludeModule " % ", InfixL () 7 ())
    , (QualifiedName preludeModule " & ", InfixR () 8 ())
    ]

preludeMacroDefs :: Map.Map Name MacroDef
preludeMacroDefs = Map.fromList
    [ (QualifiedName preludeModule "string", ([], "(list char)"))
    , (QualifiedName preludeModule "is", ([], " := "))
    ]

preludeKindDecls :: Map.Map Name KindExpr
preludeKindDecls = Map.fromList
    [ (QualifiedName preludeModule " -> ", readKind "* -> * -> *")
    , (QualifiedName preludeModule "o", readKind "*")
    , (QualifiedName preludeModule "list", readKind "* -> *")
    , (QualifiedName preludeModule "nat", readKind "*")
    , (QualifiedName preludeModule "char", readKind "*")
    ]

preludeTypeDecls :: Map.Map Name PolyType
preludeTypeDecls = Map.fromList
    [ (QualifiedName preludeModule " :- ", readType "o -> o -> o")
    , (QualifiedName preludeModule "; ", readType "o -> o -> o")
    , (QualifiedName preludeModule ", ", readType "o -> o -> o")
    , (QualifiedName preludeModule " => ", readType "o -> o -> o")
    , (QualifiedName preludeModule " = ", readType "A -> A -> o")
    , (QualifiedName preludeModule " < ", readType "A -> A -> o")
    , (QualifiedName preludeModule " > ", readType "A -> A -> o")
    , (QualifiedName preludeModule " =< ", readType "A -> A -> o")
    , (QualifiedName preludeModule " >= ", readType "A -> A -> o")
    , (QualifiedName preludeModule " := ", readType "A -> A -> o")
    , (QualifiedName preludeModule " :: ", readType "A -> list A -> list A")
    , (QualifiedName preludeModule " + ", readType "A -> A -> A")
    , (QualifiedName preludeModule " - ", readType "A -> A -> A")
    , (QualifiedName preludeModule " * ", readType "A -> A -> A")
    , (QualifiedName preludeModule " / ", readType "A -> A -> A")
    , (QualifiedName preludeModule " & ", readType "o -> o -> o")
    , (QualifiedName preludeModule "!", readType "o")
    , (QualifiedName preludeModule "true", readType "o")
    , (QualifiedName preludeModule "fail", readType "o")
    , (QualifiedName preludeModule "pi", readType "(A -> o) -> o")
    , (QualifiedName preludeModule "sigma", readType "(A -> o) -> o")
    , (QualifiedName preludeModule "[]", readType "list A")
    ]

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
        myPrecIs :: Prec -> ShowS -> ShowS
        myPrecIs prec' ss = if prec > prec' then strstr "(" . ss . strstr ")" else ss
        dispatch :: KindExpr -> ShowS
        dispatch (Star) = myPrecIs 10 $ strstr "*"
        dispatch (KArr k1 k2) = myPrecIs 0 $ pprint 5 k1 . strstr " -> " . pprint 0 k2

instance Outputable PolyType where
    pprint prec (Forall vs ty)
        | prec >= 10 = strstr "(" . go 0 vs ty . strstr ")"
        | otherwise = go prec vs ty
        where
            myPrecIs :: Prec -> Prec -> ShowS -> ShowS
            myPrecIs prec prec' ss = if prec > prec' then strstr "(" . ss . strstr ")" else ss
            go :: Prec -> [String] -> MonoType Int -> ShowS
            go prec vs (TyApp (TyApp (TyCon c) ty1) ty2)
                | c == tyArrow = myPrecIs prec 0 $ go 5 vs ty1 . strstr " -> " . go 0 vs ty2
            go prec vs (TyVar v) = myPrecIs prec 10 $ strstr (vs !! v)
            go prec vs (TyCon c) = if c == tyArrow then strstr "(->)" else myPrecIs prec 10 $ showTyCon c
            go prec vs (TyApp ty1 ty2) = myPrecIs prec 9 $ go 9 vs ty1 . strstr " " . go 10 vs ty2
            go prec vs (TyMTV u) = if unUnique u < 0 then error "pprint: TyMTV x with x < 0" else myPrecIs prec 10 $ strstr "?" . shows (unUnique u)
            showTyCon :: TypeCtor -> ShowS
            showTyCon (TypeCtor { nameOfTypeCtor = UniquelyGened uni name }) = strstr name . strstr "_" . shows uni
            showTyCon (TypeCtor { nameOfTypeCtor = QualifiedName mqual name }) = strstr name

instance Outputable Name where
    pprint _ (UniquelyGened uni name) = strstr name . strstr "_" . shows uni
    pprint _ (QualifiedName mqual name) = strstr name
