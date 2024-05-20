module Z.Utils where

import Control.Applicative
import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.State.Strict
import Control.Monad.Trans.Writer

type ErrMsg = String

type Prec = Int

type Nat = Int

newtype UniqueT m a
    = UniqueT { unUniqueT :: StateT Integer m a }
    deriving ()

newtype Unique
    = Unique { unUnique :: Integer }
    deriving (Eq, Ord, Show)

class Outputable a where
    pprint :: Prec -> a -> ShowS

class EquivRel a where
    infix 4 `equiv`
    equiv :: a -> a -> Bool

class EquivRel a => Preorder a where
    infix 4 =<
    (=<) :: a -> a -> Bool

class HasAnnot f where
    annot :: f a -> a

class Monad m => MonadUnique m where
    getUnique :: m Unique

runUniqueT :: Functor m => UniqueT m a -> m a
runUniqueT = fmap fst . flip runStateT 0 . unUniqueT

strstr :: String -> ShowS
strstr = (++)
{-# INLINABLE strstr #-}

strcat :: [ShowS] -> ShowS
strcat = foldr (.) id
{-# INLINABLE strcat #-}

pshow :: Outputable a => a -> String
pshow x = pprint 0 x ""

instance Outputable Unique where
    pprint _ (Unique i) = strstr "#" . shows i

instance Functor m => Functor (UniqueT m) where
    fmap a2b = UniqueT . fmap a2b . unUniqueT

instance Monad m => Applicative (UniqueT m) where
    pure = UniqueT . pure
    (<*>) = ap

instance Monad m => Monad (UniqueT m) where
    m >>= k = UniqueT $ unUniqueT m >>= unUniqueT . k

instance Monad m => MonadUnique (UniqueT m) where
    getUnique = UniqueT $ do
        i <- get
        i `seq` put (succ i)
        return (Unique i)

instance MonadIO m => MonadIO (UniqueT m) where
    liftIO = UniqueT . liftIO

instance MonadTrans UniqueT where
    lift = UniqueT . lift

instance MonadUnique m => MonadUnique (ExceptT e m) where
    getUnique = lift getUnique

instance MonadUnique m => MonadUnique (StateT s m) where
    getUnique = lift getUnique

instance (Monoid w, MonadUnique m) => MonadUnique (WriterT w m) where
    getUnique = lift getUnique
