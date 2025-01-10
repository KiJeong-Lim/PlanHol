module Z.System
    ( readFileNow
    , writeFileNow
    , matchFileDirWithExtension
    , makePathAbsolutely
    ) where

import Control.Monad.Fix
import Control.Monad.Trans.Class
import Control.Monad.Trans.Maybe
import System.Directory
import System.IO
import Z.Utils

infixl 1 <<

type Precedence = Int

data Flush
    = Flush
    deriving (Eq, Ord, Show)

class OStreamTrain os where
    getHandleFrom :: os -> IO Handle

class OStreamCargo a where
    hput :: Handle -> a -> IO ()

instance OStreamTrain (Handle) where
    getHandleFrom h = pure h

instance OStreamTrain a => OStreamTrain (IO a) where
    getHandleFrom h = h >>= getHandleFrom

instance OStreamCargo (Char) where
    hput = hPutChar

instance OStreamCargo a => OStreamCargo [a] where
    hput = mapM_ . hput

instance (Monoid a, OStreamCargo b) => OStreamCargo (a -> b) where
    hput h = hput h . withZero

instance OStreamCargo (Flush) where
    hput = const . hFlush

instance OStreamCargo (Int) where
    hput h = hput h . shows

instance OStreamCargo (Integer) where
    hput h = hput h . shows

instance OStreamCargo (Double) where
    hput h = hput h . shows

instance OStreamCargo (Bool) where
    hput h b = hput h (if b then "true" else "false")

matchFileDirWithExtension :: String -> (String, String)
matchFileDirWithExtension dir
    = case span (\ch -> ch /= '.') (reverse dir) of
        (reversed_extension, '.' : reversed_filename) -> (reverse reversed_filename, '.' : reverse reversed_extension)
        (reversed_filename, must_be_null) -> (reverse reversed_filename, [])

makePathAbsolutely :: FilePath -> IO (Maybe FilePath)
makePathAbsolutely = fmap (uncurry go . span (\ch -> ch /= ':')) . makeAbsolute where
    go :: String -> String -> Maybe String
    go drive path
        | take 3 path == drivesuffix = return (drive ++ path)
        | take 2 path == take 2 drivesuffix = return (drive ++ drivesuffix ++ drop 2 path)
        | otherwise = Nothing
    drivesuffix :: String
    drivesuffix = ":\\\\"

(<<) :: (OStreamTrain os, OStreamCargo a) => os -> a -> IO Handle
my_ostream << your_cargo = do
    my_handle <- getHandleFrom my_ostream
    hput my_handle your_cargo
    return my_handle

when :: Monad m => m Bool -> m a -> m (Maybe a)
when condm actionm = do
    cond <- condm
    if cond then fmap Just actionm else return Nothing

readFileNow :: FilePath -> IO (Maybe String)
readFileNow file = do
    tmp <- when (doesFileExist file) $ do
        file_permission <- getPermissions file
        if readable file_permission
            then do
                my_handle <- openFile file ReadMode
                my_handle_is_open <- hIsOpen my_handle
                my_result <- runMaybeT $ do
                    my_handle_is_okay <- if my_handle_is_open then lift (hIsReadable my_handle) else return False
                    if my_handle_is_okay
                        then do
                            my_content <- fix $ \get_content -> do
                                let my_append = foldr (fmap . kons) id
                                my_handle_is_eof <- lift (hIsEOF my_handle)
                                if my_handle_is_eof
                                    then return ""
                                    else do
                                        content1 <- lift (hGetLine my_handle)
                                        my_handle_is_still_okay <- lift (hIsReadable my_handle)
                                        content2 <- if my_handle_is_still_okay then get_content else fail ""
                                        return (my_append content1 (my_append "\n" content2))
                            callWithStrictArg return my_content
                        else fail ""
                my_result `seq` hClose my_handle
                return my_result
        else return Nothing
    callWithStrictArg return (maybe Nothing id tmp)

writeFileNow :: OStreamCargo a => FilePath -> a -> IO Bool
writeFileNow file_dir my_content = do
    my_handle <- openFile file_dir WriteMode
    my_handle_is_open <- hIsOpen my_handle
    my_handle_is_okay <- if my_handle_is_open then hIsWritable my_handle else return False
    if my_handle_is_okay
        then do
            my_handle << my_content << Flush
            hClose my_handle
            return True
        else do
            hClose my_handle
            return False
