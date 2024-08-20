{-# LANGUAGE DeriveFunctor #-}
module HOL.Ast where

import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.State.Strict
import Data.Char
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Z.Algorithms
import Z.Utils

type SmallId = String

type LargeId = String

type SPos = (Int, Int)

type MetaTVar = Unique

type MacroDef = (List String, String)

type KindVar = String

type KindExprSubst = Map.Map KindVar KindExpr

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
    = KVar !(KindVar)
    | Star
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
    = Forall (List (LargeId, KindExpr)) (MonoType Int)
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

data Module toplevel
    = Module
        { nameOfModule :: ModuleQual
        , getImporteds :: List (ModuleQual, Maybe ModuleQual)
        , getFixityEnv :: Map.Map Name (Fixity ())
        , getMacroDefs :: Map.Map Name (List String, String)
        , getKindDecls :: Map.Map Name KindExpr
        , getTypeDecls :: Map.Map Name PolyType
        , getTopLevels :: List toplevel
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
    loop 1 (c : s)
        | isLower c = one (KVar (kons c (takeWhile usual s)), dropWhile usual s)
    loop _ _ = []
    usual :: Char -> Bool
    usual c = isUpper c || isLower c || isDigit c || c == '_'

preludeModule :: ModuleQual
preludeModule = Qualed (["std"], "prelude")

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

readPolyType :: String -> PolyType
readPolyType = final . readMonoType 0 where
    usual :: Char -> Bool
    usual c = isUpper c || isLower c || isDigit c || c == '_'
    readTyVar :: ReadS String
    readTyVar (c : s)
        | isUpper c = one (c : takeWhile usual s, dropWhile usual s)
    readTyVar _ = []
    readTyCon :: ReadS String
    readTyCon (c : s)
        | isLower c = one (c : takeWhile usual s, dropWhile usual s)
    readTyCon _ = []
    maximal :: ReadS a -> ReadS [a]
    maximal p s = [ (x : xs, s'') | (x, s') <- p s, (xs, s'') <- maximal p s' ] /> one ([], s)
    readSpace :: ReadS a -> ReadS a
    readSpace p (' ' : s) = p s
    readSpace p _ = []
    readMonoType :: Prec -> ReadS (MonoType String)
    readMonoType 0 s = [ (mkTyArrow ty1 ty2, s'') | (ty1, ' ' : '-' : '>' : ' ' : s') <- readMonoType 1 s, (ty2, s'') <- readMonoType 0 s' ] /> readMonoType 1 s
    readMonoType 1 s = [ (List.foldl' TyApp ty tys, s'') | (ty, s') <- readMonoType 2 s, (tys, s'') <- maximal (readSpace (readMonoType 2)) s' ]
    readMonoType 2 s = [ (TyVar v, s') | (v, s') <- readTyVar s ] /> [ (mkTyCon tc, s') | (tc, s') <- readTyCon s ] /> readMonoType 3 s
    readMonoType _ ('(' : s) = [ (ty, s') | (ty, ')' : s') <- readMonoType 0 s ]
    readMonoType _ _ = []
    mkTyCon :: String -> MonoType String
    mkTyCon "o" = TyCon tyO
    mkTyCon "list" = TyCon tyList
    mkTyCon "nat" = TyCon tyNat
    mkTyCon "char" = TyCon tyChar
    final :: [(MonoType String, String)] -> PolyType
    final [] = error "readPolyType: no parse..."
    final [(ty, "")] = let tyvars = Set.toList (collectTyVar ty) in convert tyvars ty
    final [_] = error "readPolyType: not EOF..."
    final _ = error "readPolyType: ambiguous parses..."
    collectTyVar :: MonoType String -> Set.Set String
    collectTyVar = flip go Set.empty where
        go :: MonoType String -> Set.Set String -> Set.Set String
        go (TyVar v) = Set.insert v
        go (TyCon c) = id
        go (TyApp ty1 ty2) = go ty1 . go ty2
        go (TyMTV x) = id
    convert :: [String] -> MonoType String -> PolyType
    convert = go where
        loop :: [(String, KindExpr)] -> MonoType String -> StateT Int Maybe (MonoType Int, (KindExpr, KindExprSubst))
        loop env (TyVar v) = do
            idx <- lift $ v `List.elemIndex` map fst env
            return (TyVar idx, (snd (env !! idx), Map.empty))
        loop env (TyCon c) = return (TyCon c, (kindOfTypeCtor c, Map.empty))
        loop env (TyApp ty1 ty2) = do
            (ty1', (k1, ks1)) <- loop env ty1
            (ty2', (k2, ks2)) <- loop (map (fmap (applyKindExprSubst ks1)) env) ty2
            let ks1' = Map.map (applyKindExprSubst ks2) ks1
            i <- get
            put (1 + i)
            let kv = mkKVar i
            ks' <- lift $ getMGU ((applyKindExprSubst ks2 k1, k2 `KArr` kv) : [ (ks1' Map.! kv, ks2 Map.! kv) | kv <- Set.toList (Map.keysSet ks1' `Set.intersection` Map.keysSet ks2) ])
            return (TyApp ty1' ty2', (applyKindExprSubst ks' kv, ((ks' `Map.union` Map.map (applyKindExprSubst ks') ks2)) `Map.union` Map.map (applyKindExprSubst ks') ks1'))
        loop env (TyMTV x) = error "readPolyType: unreachable..."
        mkKVar :: Int -> KindExpr
        mkKVar i = KVar ("__KV_" ++ show i)
        go :: [String] -> MonoType String -> PolyType
        go nms ty = case runStateT (loop [ (nm, mkKVar i) | (nm, i) <- zip nms [1 .. length nms] ] ty) (1 + length nms) of
            Just ((ty', (k, ks)), _)
                | finalKindExpr k == Star -> Forall [ (nm, finalKindExpr (ks Map.! nm)) | nm <- nms ] ty'
            _ -> error "readPolyType: cannot read a polymorphic type..."
    applyKindExprSubst :: KindExprSubst -> KindExpr -> KindExpr
    applyKindExprSubst ks (KVar kv)
        | Just k <- kv `Map.lookup` ks = k
        | otherwise = KVar kv
    applyKindExprSubst ks (Star)
        = Star
    applyKindExprSubst ks (k1 `KArr` k2)
        = applyKindExprSubst ks k1 `KArr` applyKindExprSubst ks k2
    occursCheckKindExpr :: KindVar -> KindExpr -> Bool
    occursCheckKindExpr kv (KVar kv') = kv == kv'
    occursCheckKindExpr kv (Star) = False
    occursCheckKindExpr kv (k1 `KArr` k2) = occursCheckKindExpr kv k1 || occursCheckKindExpr kv k2
    unifyKindExpr :: KindExpr -> KindExpr -> Maybe KindExprSubst
    unifyKindExpr (KVar kv) (KVar kv') = if kv == kv' then return Map.empty else return $! Map.singleton kv (KVar kv')
    unifyKindExpr (KVar kv) k = if occursCheckKindExpr kv k then Nothing else return $! Map.singleton kv k
    unifyKindExpr k (KVar kv) = if occursCheckKindExpr kv k then Nothing else return $! Map.singleton kv k
    unifyKindExpr (Star) (Star) = return Map.empty
    unifyKindExpr (k1 `KArr` k2) (k1' `KArr` k2') = do
        ks1 <- unifyKindExpr k1 k1'
        ks2 <- unifyKindExpr (applyKindExprSubst ks1 k2) (applyKindExprSubst ks1 k2')
        return (composeKindExprSubst ks1 ks2)
    unifyKindExpr _ _ = Nothing
    composeKindExprSubst :: KindExprSubst -> KindExprSubst -> KindExprSubst
    composeKindExprSubst ks1 ks2 = Map.union (Map.map (applyKindExprSubst ks2) ks1) ks2
    getMGU :: [(KindExpr, KindExpr)] -> Maybe KindExprSubst
    getMGU [] = return Map.empty
    getMGU ((lhs, rhs) : eqns) = do
        ks <- unifyKindExpr lhs rhs
        ks' <- getMGU (zip (map (applyKindExprSubst ks . fst) eqns) (map (applyKindExprSubst ks . snd) eqns))
        return (composeKindExprSubst ks ks')
    finalKindExpr :: KindExpr -> KindExpr
    finalKindExpr (KVar _) = Star
    finalKindExpr (Star) = Star
    finalKindExpr (k1 `KArr` k2) = finalKindExpr k1 `KArr` finalKindExpr k2

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
    [ (QualifiedName preludeModule " :- ", readPolyType "o -> o -> o")
    , (QualifiedName preludeModule "; ", readPolyType "o -> o -> o")
    , (QualifiedName preludeModule ", ", readPolyType "o -> o -> o")
    , (QualifiedName preludeModule " => ", readPolyType "o -> o -> o")
    , (QualifiedName preludeModule " = ", readPolyType "A -> A -> o")
    , (QualifiedName preludeModule " < ", readPolyType "A -> A -> o")
    , (QualifiedName preludeModule " > ", readPolyType "A -> A -> o")
    , (QualifiedName preludeModule " =< ", readPolyType "A -> A -> o")
    , (QualifiedName preludeModule " >= ", readPolyType "A -> A -> o")
    , (QualifiedName preludeModule " := ", readPolyType "A -> A -> o")
    , (QualifiedName preludeModule " :: ", readPolyType "A -> list A -> list A")
    , (QualifiedName preludeModule " + ", readPolyType "A -> A -> A")
    , (QualifiedName preludeModule " - ", readPolyType "A -> A -> A")
    , (QualifiedName preludeModule " * ", readPolyType "A -> A -> A")
    , (QualifiedName preludeModule " / ", readPolyType "A -> A -> A")
    , (QualifiedName preludeModule " & ", readPolyType "o -> o -> o")
    , (QualifiedName preludeModule "!", readPolyType "o")
    , (QualifiedName preludeModule "true", readPolyType "o")
    , (QualifiedName preludeModule "fail", readPolyType "o")
    , (QualifiedName preludeModule "pi", readPolyType "(A -> o) -> o")
    , (QualifiedName preludeModule "sigma", readPolyType "(A -> o) -> o")
    , (QualifiedName preludeModule "[]", readPolyType "list A")
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
        dispatch (KVar kv) = strstr kv
        dispatch (Star) = myPrecIs 10 $ strstr "*"
        dispatch (KArr k1 k2) = myPrecIs 0 $ pprint 5 k1 . strstr " -> " . pprint 0 k2

instance Outputable PolyType where
    pprint prec (Forall vs ty)
        | prec >= 10 = strstr "(" . go 0 (map fst vs) ty . strstr ")"
        | otherwise = go prec (map fst vs) ty
        where
            myPrecIs :: Prec -> Prec -> ShowS -> ShowS
            myPrecIs prec prec' ss = if prec > prec' then strstr "(" . ss . strstr ")" else ss
            go :: Prec -> [String] -> MonoType Int -> ShowS
            go prec vs (TyApp (TyApp (TyCon c) ty1) ty2)
                | c == tyArrow = myPrecIs prec 0 $ go 5 vs ty1 . strstr " -> " . go 0 vs ty2
            go prec vs (TyVar v) = myPrecIs prec 10 $ strstr (vs !! v)
            go prec vs (TyCon c) = if c == tyArrow then strstr "(->)" else myPrecIs prec 10 $ showTyCon c
            go prec vs (TyApp ty1 ty2) = myPrecIs prec 9 $ go 9 vs ty1 . strstr " " . go 10 vs ty2
            go prec vs (TyMTV u) = if unUnique u < 0 then error "pprint: TyMTV x with x < 0" else myPrecIs prec 10 $ strstr "?TV_" . shows (unUnique u)
            showTyCon :: TypeCtor -> ShowS
            showTyCon (TypeCtor { nameOfTypeCtor = UniquelyGened uni name }) = strstr name . strstr "_" . shows uni
            showTyCon (TypeCtor { nameOfTypeCtor = QualifiedName mqual name }) = strstr name

instance Outputable Name where
    pprint _ (UniquelyGened uni name) = strstr name . strstr "_#" . shows uni
    pprint _ (QualifiedName mqual name) = strstr name
