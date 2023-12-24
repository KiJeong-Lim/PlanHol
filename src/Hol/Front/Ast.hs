module Hol.Front.Ast where

import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.State.Strict
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Z.Utils

type SmallId = String

type LargeId = String

type SymbolId = String

type Keyword = String

type Unique = Integer

type IVar = Unique

type MTVar = Unique

type SrcPos = (Int, Int)

type ErrMsgBox = [(String, String)]

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

instance Semigroup SrcLoc where
    SrcLoc pos1 pos2 <> SrcLoc pos1' pos2' = SrcLoc (min pos1 pos1') (max pos2 pos2')

instance Outputable SrcLoc where
    pprint _ (SrcLoc { locLeft = (r1, c1), locRight = (r2, c2) }) = shows r1 . strstr ":" . shows c1 . strstr "-" . shows r2 . strstr ":" . shows c2

instance Functor (TermExpr dcon) where
    fmap a2b (Var a x) = Var (a2b a) x
    fmap a2b (Con a c) = Con (a2b a) c
    fmap a2b (App a t1 t2) = App (a2b a) (fmap a2b t1) (fmap a2b t2)
    fmap a2b (Lam a x t1) = Lam (a2b a) x (fmap a2b t1)

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
        let n' = n + 1
        n' `seq` put n'
        return n

instance MonadUnique m => MonadUnique (ExceptT s m) where
    newUnique = lift newUnique

instance MonadUnique m => MonadUnique (StateT s m) where
    newUnique = lift newUnique
