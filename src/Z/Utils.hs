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

type List = []

type Indentation = Int

newtype UniqueT m a
    = UniqueT { runUniqueT :: StateT Integer m a }
    deriving ()

newtype Unique
    = Unique { unUnique :: Integer }
    deriving (Eq, Ord, Show)

class Outputable a where
    pprint :: Prec -> a -> ShowS

class HasAnnot f where
    getAnnot :: f a -> a
    setAnnot :: a -> f a -> f a

class Monad m => MonadUnique m where
    getUnique :: m Unique

withZero :: Monoid a => (a -> b) -> b
withZero to_be_initialized = to_be_initialized mempty

execUniqueT :: Functor m => UniqueT m a -> m a
execUniqueT = fmap fst . flip runStateT 0 . runUniqueT
{-# INLINABLE execUniqueT #-}

strstr :: String -> ShowS
strstr = (++)
{-# INLINABLE strstr #-}

strcat :: [ShowS] -> ShowS
strcat = foldr (.) id
{-# INLINABLE strcat #-}

pshow :: Outputable a => a -> String
pshow x = pprint 0 x ""
{-# INLINABLE pshow #-}

callWithStrictArg :: (a -> b) -> a -> b
callWithStrictArg f x = f $! x

one :: a -> [a]
one = callWithStrictArg pure

nl :: ShowS
nl = showString "\n"

pindent :: Indentation -> ShowS
pindent space = if space < 0 then id else showString (replicate space ' ')

ppunc :: String -> [ShowS] -> ShowS
ppunc str deltas = if null deltas then id else head deltas . foldr (\delta -> \acc -> strstr str . delta . acc) id (tail deltas)

plist' :: Indentation -> [ShowS] -> ShowS
plist' space deltas = nl . pindent space . strstr "[ " . ppunc (withZero (nl . pindent space . strstr ", ")) deltas . nl . pindent space . strstr "]"

plist :: Indentation -> [ShowS] -> ShowS
plist space deltas = if null deltas then strstr "[]" else plist' space deltas

quotify :: ShowS -> ShowS
quotify = shows . withZero

plist1 :: Indentation -> [ShowS] -> ShowS
plist1 space [] = strstr "[]"
plist1 space [delta] = strstr "[" . delta . strstr "]"
plist1 space deltas = plist' space deltas

instance Outputable Integer where
    pprint prec = if prec == 0 then byDigitsOf 3 else shows where
        byDigitsOf :: Int -> Integer -> ShowS
        byDigitsOf k n
            | n < 0 = strstr "- " . byDigitsOf k (negate n)
            | otherwise = if n >= (10 ^ k) then byDigitsOf k (n `div` (10 ^ k)) . strstr " " . strcat [ shows ((n `div` (10 ^ i)) `mod` 10) | i <- [k - 1, k - 2 .. 0] ] else shows n

instance Outputable Unique where
    pprint _ (Unique i) = strstr "#" . shows i

instance Functor m => Functor (UniqueT m) where
    fmap a2b = UniqueT . fmap a2b . runUniqueT

instance Monad m => Applicative (UniqueT m) where
    pure = UniqueT . pure
    (<*>) = ap

instance Monad m => Monad (UniqueT m) where
    m >>= k = UniqueT $ runUniqueT m >>= runUniqueT . k

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
