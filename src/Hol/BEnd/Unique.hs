{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Hol.BEnd.Base where

import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.Reader
import Control.Monad.Trans.State.Strict
import Control.Monad.Trans.Writer.Strict

type Unique = Integer

newtype UniqueT m a
    = UniqueT { unUniqueT :: StateT Unique m a }
    deriving (Functor, Applicative, Monad, MonadTrans, MonadIO, MonadFail)

class (Monad m) => MonadU m where
    new :: m Unique

runUniqueT :: (Functor m) => UniqueT m a -> m a
runUniqueT = fmap fst . flip runStateT 0 . unUniqueT

instance (Monad m) => MonadU (UniqueT m) where
    new = UniqueT $ do
        u <- get
        let u' = succ u
        u' `seq` put u'
        return u'

instance (MonadU m) => MonadU (ExceptT e m) where
    new = ExceptT $ fmap Right new

instance (MonadU m) => MonadU (ReaderT r m) where
    new = ReaderT $ const new

instance (MonadU m) => MonadU (StateT s m) where
    new = StateT $ \s -> do
        u <- new
        return (u, s)

instance (Monoid w, MonadU m) => MonadU (WriterT w m) where
    new = WriterT $ do
        u <- new
        return (u, mempty)
