module Hol.Front.Ast where

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

type SymbolId = String

type Keyword = String

type Unique = Integer

type MTVar = Identifier

type Predicate = Identifier

type SrcPos = (Int, Int)

type ErrMsgBox = [(String, String)]

type KindEnv = Map.Map TCon KindExpr

type TypeEnv = Map.Map DCon PolyType

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
    = IdOnlyName { idName :: String }
    | IdWithUnique { idName :: String, idUnique :: Unique }
    | IdOnlyUnique { idUnique :: Unique }
    deriving (Eq, Ord, Show)

data Literal
    = LitNat Integer
    | LitChr Char
    | LitStr String
    deriving (Eq, Ord, Show)

data KindExpr
    = KindStar
    | KindArrow KindExpr KindExpr
    deriving (Eq, Ord)

data LogicalOperator
    = LoTyPi
    | LoIf
    | LoTrue
    | LoFail
    | LoCut
    | LoAnd
    | LoOr
    | LoImply
    | LoForall
    | LoExists
    deriving (Eq, Ord, Show)

data DCon
    = DConLo LogicalOperator
    | DConId Predicate
    | DConNil
    | DConCons
    | DConChrL Char
    | DConNatL Integer
    | DConSucc
    | DConEq
    | DCWildCard
    deriving (Eq, Ord, Show)

data TermExpr dcon annot
    = Var annot Identifier
    | Con annot dcon
    | App annot (TermExpr dcon annot) (TermExpr dcon annot)
    | Lam annot Identifier (TermExpr dcon annot)
    deriving (Eq, Ord, Show)

data TCon
    = TCon Identifier KindExpr
    deriving (Eq, Ord, Show)

data MonoType tvar
    = TyVar tvar
    | TyCon TCon
    | TyApp (MonoType tvar) (MonoType tvar)
    | TyMTV Identifier
    deriving (Eq, Ord, Show)

data PolyType
    = Forall [Identifier] (MonoType Int)
    deriving (Eq, Ord, Show)

data Module term
    = Module
        { moduleName :: String
        , _KindDecls :: KindEnv
        , _TypeDecls :: TypeEnv
        , _FactDecls :: [(Predicate, [term])]
        , _SymbolTbl :: [SymbolRep ()]
        }
    deriving (Eq, Ord, Show)

newtype UniqueT m a
    = UniqueT { runUniqueT :: StateT Unique m a }
    deriving ()

class Monad m => MonadUnique m where
    newUnique :: m Unique

getSymbolPrec :: SymbolRep a -> Prec
getSymbolPrec (Prefix prec _ _) = prec
getSymbolPrec (InfixL prec _ _ _) = prec
getSymbolPrec (InfixR prec _ _ _) = prec
getSymbolPrec (InfixO prec _ _ _) = prec

execUniqueT :: Functor m => UniqueT m a -> m a
execUniqueT = fmap fst . flip runStateT 0 . runUniqueT

mkTyList :: MonoType tvar -> MonoType tvar
mkTyList = TyApp (TyCon (TCon (IdOnlyName "List") (read "* -> *")))

mkTyChr :: MonoType tvar
mkTyChr = TyCon (TCon (IdOnlyName "Char") (read "*"))

mkTyNat :: MonoType tvar
mkTyNat = TyCon (TCon (IdOnlyName "Nat") (read "*"))

mkTyProp :: MonoType tvar
mkTyProp = TyCon (TCon (IdOnlyName "Prop") (read "*"))

mkTyArrow :: MonoType tvar -> MonoType tvar -> MonoType tvar
typ1 `mkTyArrow` typ2 = TyApp (TyApp (TyCon (TCon (IdOnlyName "->") (read "* -> * -> *"))) typ1) typ2

instance Semigroup SrcLoc where
    SrcLoc pos1 pos2 <> SrcLoc pos1' pos2' = SrcLoc { locLeft = min pos1 pos1', locRight = max pos2 pos2' }

instance Outputable SrcLoc where
    pprint _ (SrcLoc { locLeft = (r1, c1), locRight = (r2, c2) }) = shows r1 . strstr ":" . shows c1 . strstr "-" . shows r2 . strstr ":" . shows c2

instance Functor SymbolRep where
    fmap a2b (Prefix prec a1 sym) = Prefix prec (a2b a1) sym
    fmap a2b (InfixL prec a1 sym a2) = InfixL prec (a2b a1) sym (a2b a2)
    fmap a2b (InfixR prec a1 sym a2) = InfixR prec (a2b a1) sym (a2b a2)
    fmap a2b (InfixO prec a1 sym a2) = InfixO prec (a2b a1) sym (a2b a2)

instance Outputable Literal where
    pprint _ (LitNat n) = shows n
    pprint _ (LitChr ch) = shows ch
    pprint _ (LitStr s) = shows s

instance Show KindExpr where
    showsPrec _ KindStar = strstr "*"
    showsPrec 0 (KindArrow k1 k2) = showsPrec 1 k1 . strstr " -> " . shows k2
    showsPrec _ k = strstr "(" . shows k . strstr ")"

instance Read KindExpr where
    readsPrec 0 s0 = [ (k1 `KindArrow` k2, s2) | (k1, ' ' : '-' : '>' : ' ' : s1) <- readsPrec 1 s0, (k2, s2) <- reads s1 ] ++ readsPrec 1 s0
    readsPrec _ ('*' : s0) = [(KindStar, s0)]
    readsPrec _ ('(' : s0) = [ (k, s1) | (k, ')' : s1) <- reads s0 ]
    readsPrec _ _ = []
    readList = undefined

instance Functor (TermExpr dcon) where
    fmap a2b (Var a x) = Var (a2b a) x
    fmap a2b (Con a c) = Con (a2b a) c
    fmap a2b (App a t1 t2) = App (a2b a) (fmap a2b t1) (fmap a2b t2)
    fmap a2b (Lam a x t1) = Lam (a2b a) x (fmap a2b t1)

instance Functor MonoType where
    fmap a2b (TyVar a) = TyVar (a2b a)
    fmap a2b (TyCon c) = TyCon c
    fmap a2b (TyApp ty1 ty2) = TyApp (fmap a2b ty1) (fmap a2b ty2)
    fmap a2b (TyMTV mtv) = TyMTV mtv

instance Functor m => Functor (UniqueT m) where
    fmap a2b = UniqueT . fmap a2b . runUniqueT

instance Monad m => Applicative (UniqueT m) where
    pure a = UniqueT (pure a)
    fa2b <*> fa = UniqueT (runUniqueT fa2b <*> runUniqueT fa)

instance Monad m => Monad (UniqueT m) where
    m >>= k = UniqueT (runUniqueT m >>= \a -> runUniqueT (k a))

instance MonadTrans UniqueT where
    lift = UniqueT . lift

instance MonadFail m => MonadFail (UniqueT m) where
    fail = UniqueT . fail

instance MonadIO m => MonadIO (UniqueT m) where
    liftIO = UniqueT . liftIO

instance Monad m => MonadUnique (UniqueT m) where
    newUnique = UniqueT $ do
        n <- get
        let n' = succ n
        n' `seq` put n'
        return n

instance MonadUnique m => MonadUnique (ExceptT s m) where
    newUnique = lift newUnique

instance MonadUnique m => MonadUnique (StateT s m) where
    newUnique = lift newUnique

instance MonadUnique m => MonadUnique (ReaderT s m) where
    newUnique = lift newUnique
