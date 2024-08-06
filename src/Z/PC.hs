{-# LANGUAGE DeriveFunctor #-}
module Z.PC where

import Control.Applicative
import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Fail
import Control.Monad.Trans.State.Strict
import Control.Monad.Trans.Maybe
import Data.Function
import Data.Functor
import Data.List as List
import System.IO
import System.Console.Pretty
import System.Directory
import Z.Algorithms
import Z.Doc
import Z.Utils

type LocString = List LocChar

type P = PC LocChar

data PC char val
    = PcVal (val)
    | PcAct (List char -> [(PC char val, List char)])
    deriving (Functor)

data CharSet char
    = CsUniv
    | CsPlus (CharSet char) (CharSet char)
    | CsDiff (CharSet char) (CharSet char)
    | CsEnum (char) (char)
    | CsAtom (char)
    deriving (Eq, Ord, Show, Functor)

data RegEx char
    = ReCSet (CharSet char)
    | ReWord (List char)
    | RePlus (RegEx char) (RegEx char)
    | ReZero
    | ReMult (RegEx char) (RegEx char)
    | ReStar (RegEx char)
    deriving (Eq, Ord, Show, Functor)

newtype BP c a
    = BP { runBP :: List c -> [(a, List c)] }
    deriving (Functor)

data LocChar
    = LocChar { locOfLocChar :: (Int, Int), charOfLocChar :: !Char }
    deriving (Eq, Ord, Show)

class ParserCombinator p where
    eval :: p c a -> List c -> [(a, List c)]
    auto :: Read a => Prec -> p Char a
    char :: (c -> Bool) -> p c c
    consume :: Eq c => List c -> p c ()
    match :: Eq c => List c -> p c ()
    eof :: p c ()
    neg :: p c a -> p c ()
    kstar :: p c a -> p c [a]

mkCsUniv :: CharSet c
mkCsUniv = CsUniv

mkCsPlus :: CharSet c -> CharSet c -> CharSet c
mkCsPlus cs1 cs2 = (CsPlus $! cs1) $! cs2

mkCsDiff :: CharSet c -> CharSet c -> CharSet c
mkCsDiff cs1 cs2 = (CsDiff $! cs1) $! cs2

mkCsEnum :: c -> c -> CharSet c
mkCsEnum c1 c2 = (CsEnum $! c1) $! c2

mkCsAtom :: c -> CharSet c
mkCsAtom c1 = CsAtom $! c1

mkReCSet :: CharSet c -> RegEx c
mkReCSet cs = ReCSet $! cs

mkReWord :: List c -> RegEx c
mkReWord s = ReWord $! s

mkRePlus :: RegEx c -> RegEx c -> RegEx c
mkRePlus (ReZero) re2 = re2
mkRePlus re1 (ReZero) = re1
mkRePlus re1 re2 = RePlus re1 re2

mkReZero :: RegEx c
mkReZero = ReZero

mkReMult :: RegEx c -> RegEx c -> RegEx c
mkReMult (ReWord []) re2 = re2
mkReMult re1 (ReWord []) = re1
mkReMult (ReWord s1) (ReWord s2) = mkReWord (s1 ++ s2)
mkReMult (ReZero) re2 = mkReZero
mkReMult re1 (ReZero) = mkReZero
mkReMult re1 re2 = ReMult re1 re2

mkReStar :: RegEx c -> RegEx c
mkReStar (ReZero) = mkReWord []
mkReStar (ReWord []) = mkReWord []
mkReStar (ReStar re11) = mkReStar re11
mkReStar re1 = ReStar re1

isInCharSet :: (Eq c, Enum c) => c -> CharSet c -> Bool
isInCharSet c (CsUniv) = True
isInCharSet c (CsPlus cs1 cs2) = isInCharSet c cs1 || isInCharSet c cs2
isInCharSet c (CsDiff cs1 cs2) = isInCharSet c cs1 && not (isInCharSet c cs2)
isInCharSet c (CsEnum c1 c2) = c `elem` [c1 .. c2]
isInCharSet c (CsAtom c1) = c == c1

maximalMunchPC :: RegEx Char -> LocString -> Maybe (String, LocString)
maximalMunchPC = go where
    isNullable :: RegEx Char -> Bool
    isNullable (ReCSet chs) = False
    isNullable (ReWord str) = null str
    isNullable (RePlus re1 re2) = isNullable re1 || isNullable re2
    isNullable (ReZero) = False
    isNullable (ReMult re1 re2) = isNullable re1 && isNullable re2
    isNullable (ReStar re1) = True
    differentiate :: Char -> (RegEx Char -> RegEx Char)
    differentiate ch (ReCSet chs)
        | isInCharSet ch chs = mkReWord ""
        | otherwise = mkReZero
    differentiate ch (ReWord str)
        | [ch] == take 1 str = mkReWord (tail str)
        | otherwise = mkReZero
    differentiate ch (RePlus re1 re2)
        = mkRePlus (differentiate ch re1) (differentiate ch re2)
    differentiate ch (ReZero)
        = mkReZero
    differentiate ch (ReMult re1 re2)
        | isNullable re1 = mkRePlus (differentiate ch re2) (mkReMult (differentiate ch re1) re2)
        | otherwise = mkReMult (differentiate ch re1) re2
    differentiate ch (ReStar re1)
        = mkReMult (differentiate ch re1) (mkReStar re1)
    isNotEmpty :: CharSet Char -> Bool
    isNotEmpty _ = True
    mayPlvsVltra :: RegEx Char -> Bool
    mayPlvsVltra (ReCSet chs) = isNotEmpty chs
    mayPlvsVltra (ReWord str) = not (null str)
    mayPlvsVltra (RePlus re1 re2) = or
        [ mayPlvsVltra re1
        , mayPlvsVltra re2
        ]
    mayPlvsVltra (ReZero) = False
    mayPlvsVltra (ReMult re1 re2) = or
        [ mayPlvsVltra re1 && mayPlvsVltra re2
        , mayPlvsVltra re1 && isNullable re2
        , isNullable re1 && mayPlvsVltra re2
        ]
    mayPlvsVltra (ReStar re1) = mayPlvsVltra re1
    repeatPlvsVltra :: String -> RegEx Char -> StateT (LocString) Maybe (String, RegEx Char)
    repeatPlvsVltra output regex = do
        buffer <- get
        case buffer of
            [] -> if isNullable regex
                then return (output, regex)
                else fail ""
            (LocChar _ ch : buffer') -> do
                put buffer'
                let regex' = differentiate ch regex
                    output' = ch : output
                if isNullable regex'
                    then return (output', regex')
                    else if mayPlvsVltra regex'
                        then repeatPlvsVltra output' regex'
                        else fail "It is impossible that I read the buffer further more and then accept the given regex."
    getBuffer :: (LocString, String) -> LocString
    getBuffer commit = fst commit
    getOutput :: (LocString, String) -> String
    getOutput commit = snd commit
    runRegEx :: RegEx Char -> (LocString, String) -> (LocString, String)
    runRegEx current_regex last_commit
        = case runStateT (repeatPlvsVltra "" current_regex) (getBuffer last_commit) of
            Nothing -> last_commit
            Just ((revesed_token_of_output, next_regex), new_buffer)
                | null new_buffer -> commit
                | otherwise -> runRegEx next_regex commit
                where
                    commit :: (LocString, String)
                    commit = (new_buffer, getOutput last_commit ++ reverse revesed_token_of_output)
    go :: RegEx Char -> LocString -> Maybe (String, LocString)
    go regex lstr0 = case runRegEx regex (lstr0, "") of
        (lstr1, output) -> if not (null output) || isNullable regex then return (output, lstr1) else Nothing

regexPC :: String -> P String
regexPC regex_representation = maybe (error $ "Z.PC.regexPC: invalid-regex-representation-is-given, regex-representation=" ++ shows regex_representation ".\n") (\regex -> PcAct $ map (uncurry $ (,) . PcVal) . (maybe [] pure . maximalMunchPC regex)) $ readRegEx regex_representation

intPC :: P Int
intPC = read <$> regexPC "['-']? ['0'-'9']+"

acceptQuote :: P String
acceptQuote = pure read <*> regexPC "\"\\\"\" (\"\\\\\" [\'n\' \'t\' \'\"\' \'\\\\\' \'\\\'\'] + [.\\\'\\n\'\\\'\\t\'\\\'\\\"\'\\\'\\\\\'])* \"\\\"\""

skipWhite :: P Int
skipWhite = PcAct $ \s -> case span (\lch -> charOfLocChar lch == ' ') s of
    (ws, s') -> one (PcVal $! length ws, s')

smallid :: P String
smallid = regexPC "[\'a\'-\'z\'] [\'a\'-\'z\' \'0\'-\'9\' \'_\']*"

largeid :: P String
largeid = regexPC "[\'A\'-\'Z\'] [\'a\'-\'z\' \'0\'-\'9\' \'A\'-\'Z\']*"

puncPC :: String -> P val -> P [val]
puncPC str p = (pure (:) <*> p <*> many (consumePC str *> p)) <|> pure []

parenPC :: Char -> Char -> P val -> P val
parenPC ch1 ch2 p = acceptPC (\ch -> ch == ch1) *> p <* acceptPC (\ch -> ch == ch2)

lend :: P ()
lend = skipWhite *> consumePC "\n"

indent :: Int -> P ()
indent n = consumePC (replicate n ' ')

charPC :: P Char
charPC = pure read <*> regexPC "\"\\\'\" (\"\\\\\" [\'n\' \'t\' \'\"\' \'\\\\\' \'\\\'\'] + [.\\\'\\n\'\\\'\\t\'\\\'\\\"\'\\\'\\\\\']) \"\\\'\""

acceptList :: P a -> P [a]
acceptList pc = consumePC "[" *> (skipWhite *> (pure [] <|> (pure (:) <*> pc <*> many (consumePC "," *> skipWhite *> pc)))) <* consumePC "]"

acceptPC :: (Char -> Bool) -> P Char
acceptPC cond = PcAct $ \s -> if null s then [] else let ch = charOfLocChar (head s) in if cond ch then one (PcVal ch, tail s) else [] 

consumePC :: List Char -> P ()
consumePC prefix = PcAct $ \s -> let n = length prefix in if map charOfLocChar (take n s) == prefix then one (PcVal (), drop n s) else []

matchPC :: List Char -> P ()
matchPC prefix = PcAct $ \s -> let n = length prefix in if map charOfLocChar (take n s) == prefix then one (PcVal (), s) else []

eofPC :: P ()
eofPC = PcAct $ \s -> if null s then one (PcVal (), s) else []

negPC :: P a -> P ()
negPC parser = do
    p_has_parse <- (parser $> True) /> return False
    when p_has_parse empty

parseCharSet :: Prec -> BP Char (CharSet Char) 
parseCharSet 0 = List.foldl' mkCsDiff <$> parseCharSet 1 <*> many (consume "\\" *> parseCharSet 2)
parseCharSet 1 = List.foldl' mkCsPlus <$> parseCharSet 2 <*> many (consume " " *> parseCharSet 2)
parseCharSet 2 = mconcat
    [ mkCsAtom <$> auto 0
    , mkCsEnum <$> auto 0 <* consume "-" <*> auto 0
    , consume "." $> mkCsUniv
    , parseCharSet 3
    ]
parseCharSet _ = consume "(" *> parseCharSet 0 <* consume ")"

parseRegEx :: Prec -> BP Char (RegEx Char)
parseRegEx = go where
    mkDagger :: RegEx c -> RegEx c
    mkDagger re = mkReMult re (mkReStar re)
    mkQuest :: RegEx c -> RegEx c
    mkQuest re = mkRePlus re (mkReWord [])
    suffix :: BP Char (RegEx Char -> RegEx Char)
    suffix = mconcat
        [ consume "*" $> mkReStar
        , consume "+" $> mkDagger
        , consume "?" $> mkQuest
        ]
    go :: Prec -> BP Char (RegEx Char)
    go 0 = List.foldl' mkRePlus <$> go 1 <*> many (consume " + " *> go 1)
    go 1 = List.foldl' mkReMult <$> go 2 <*> many (consume " " *> go 2)
    go 2 = List.foldl' (flip ($)) <$> go 3 <*> many suffix
    go 3 = mconcat
        [ consume "[" *> (mkReCSet <$> parseCharSet 0) <* consume "]"
        , mkReWord <$ match "\"" <*> auto 0
        , consume "()" $> mkReZero
        , go 4
        ]
    go _ = consume "(" *> go 0 <* consume ")"

readCharSet :: String -> Maybe (CharSet Char)
readCharSet = safehd . map fst . runBP (parseCharSet 0 <* eof)

readRegEx :: String -> Maybe (RegEx Char)
readRegEx = safehd . map fst . runBP (parseRegEx 0 <* eof)

returnPC :: a -> PC c a
returnPC = PcVal

bindPC :: PC c a -> (a -> PC c a') -> PC c a'
bindPC (PcVal x) k = k x
bindPC (PcAct p) k = PcAct $ \s -> [ (bindPC m k, s') | (m, s') <- p s ]

evalPC :: PC c a -> List c -> [(a, List c)]
evalPC (PcVal x) = curry return x
evalPC (PcAct p) = uncurry evalPC <=< p

execPC :: PC c a -> List c -> Either (List c) a
execPC = go where
    findShortest :: [[a]] -> [a]
    findShortest = head . mSort ((<=) `on` length)
    loop :: PC c a -> List c -> Either (List c) [(a, List c)]
    loop (PcVal x) s = return [(x, s)]
    loop (PcAct p) s
        | null res = Left $! s
        | otherwise = if null oks then Left $! findShortest nos else return oks
        where
            res = [ loop m s' | (m, s') <- p s ]
            oks = [ (x, s'') | Right ok <- res, (x, s'') <- ok ]
            nos = [ s' | Left s' <- res ]
    go :: PC c a -> List c -> Either (List c) a
    go m s = do
        res <- loop m s
        oks <- if null res then Left $! s else return [ x | (x, []) <- res ]
        case oks of
            [] -> Left $! findShortest (map snd res)
            x : _ -> return x

runP :: FilePath -> P a -> IO (Maybe a)
runP path = runMaybeT . parseFile where
    loadFile :: MaybeT IO LocString
    loadFile = do
        b <- liftIO $ doesFileExist path
        when (not b) (fail "There is no such file")
        h <- liftIO $ openFile path ReadMode
        b <- liftIO $ hIsOpen h
        when (not b) (fail "The file is not open")
        b <- liftIO $ hIsReadable h
        when (not b) (fail "The file is non-readable")
        let loop = hIsEOF h >>= \b -> if b then return [] else kons <$> hGetChar h <*> loop
            addLoc r c [] = []
            addLoc r c (ch : ss)
                | ch == '\n' = r `seq` c `seq` (LocChar (r, c) ch `kons` addLoc (succ r) 1 ss)
                | ch == '\t' = r `seq` c `seq` (LocChar (r, c) ch `kons` addLoc r (calcTab 1 c) ss) 
                | otherwise = r `seq` c `seq` (LocChar (r, c) ch `kons` addLoc r (succ c) ss)
        lstr <- addLoc initRow initCol <$> liftIO loop
        lstr `seq` (liftIO $ hClose h)
        return lstr
    initRow :: Int
    initRow = 1
    initCol :: Int
    initCol = 1
    calcTab :: Int -> Int -> Int
    calcTab tab_sz c = if tab_sz <= 1 then succ c else tab_sz - (c `mod` tab_sz) + c
    mkErrorMsg :: Bool -> String -> LocString -> Doc
    mkErrorMsg is_pretty src lstr
        | is_pretty = version1
        | otherwise = version2
        where
            stuckRow :: Int
            stuckRow = case lstr of
                [] -> length (filter (\lch -> charOfLocChar lch == '\n') lstr) + initRow
                LocChar (r, c) ch : _ -> r
            stuckCol :: Int
            stuckCol = case lstr of
                [] -> length stuckLine + initCol
                LocChar (r, c) ch : _ -> r
            stuckLine :: String
            stuckLine = splitBy '\n' src !! (stuckRow - initRow)
            version1 :: Doc
            version1 = vcat
                [ textbf (path ++ ":" ++ pprint 0 stuckRow (":" ++ pprint 0 stuckCol ": ")) <> red (textbf "error:")
                , textbf "parse error " <> (if null lstr then textbf "at EOF" else textbf "on input `" <> ptext (charOfLocChar (head lstr)) <> text "'")
                , mconcat
                    [ vcat [text " ", mconcat [text " ", blue (textbf (show stuckRow)), text " "], text " "]
                    , blue (beam '|')
                    , vcat [text " ", text " " <> text stuckLine, text " " <> text (replicate (stuckCol - initCol) ' ') <> red (textbf "^")]
                    ]
                ]
            version2 :: Doc
            version2 = vcat
                [ text path <> text ":" <> ptext stuckRow <> text ":" <> ptext stuckCol <> text ": error:"
                , text "parse error " <> (if null lstr then text "at EOF" else text "on input `" <> ptext (charOfLocChar (head lstr)) <> text "'")
                , mconcat
                    [ vcat [text "", mconcat [text " ", ptext stuckRow, text " "], text ""]
                    , beam '|'
                    , vcat [text " ", text " " <> text stuckLine, text " " <> text (replicate (stuckCol - initCol) ' ') <> textbf "^"]
                    ]
                ]
    parseFile :: P a -> MaybeT IO a
    parseFile parser = do
        b <- liftIO supportsPretty
        s <- loadFile
        case execPC parser s of
            Right x -> return x
            Left s' -> do
                let msg = mkErrorMsg b (map charOfLocChar s) s'
                liftIO . putStrLn $! renderDoc msg
                fail "runP: failed..."

returnBP :: a -> BP c a
returnBP = BP . curry return

bindBP :: BP c a -> (a -> BP c a') -> BP c a'
bindBP m k = BP $ runBP m >=> uncurry (runBP . k)

instance ParserCombinator PC where
    eval = evalPC
    auto prec = PcAct $ map (uncurry $ (,) . PcVal) . readsPrec prec
    char cond = PcAct $ \s -> if null s then [] else let c = head s in if cond c then one (PcVal c, tail s) else []
    consume prefix = PcAct $ \s -> let n = length prefix in if take n s == prefix then one (PcVal (), drop n s) else []
    match prefix = PcAct $ \s -> let n = length prefix in if take n s == prefix then one (PcVal (), s) else []
    eof = PcAct $ \s -> if null s then one (PcVal (), s) else []
    neg parser = do
        p_has_parse <- (parser $> True) /> return False
        when p_has_parse empty
    kstar parser = pure [] <|> ((:) <$> parser <*> kstar parser)

instance ParserCombinator BP where
    eval = runBP
    auto prec = BP $ readsPrec prec
    char cond = BP $ \s -> if null s then [] else let c = head s in if cond c then one (c, tail s) else []
    consume prefix = BP $ \s -> let n = length prefix in if take n s == prefix then one ((), drop n s) else []
    match prefix = BP $ \s -> let n = length prefix in if take n s == prefix then one ((), s) else []
    eof = BP $ \s -> if null s then one ((), s) else []
    neg parser = BP $ \s -> if null $ runBP parser s then [] else one ((), s)
    kstar parser = pure [] <|> ((:) <$> parser <*> kstar parser)

instance Applicative (PC c) where
    pure = returnPC
    (<*>) = ap

instance Monad (PC c) where
    (>>=) = bindPC

instance Alternative (PC c) where
    m1 <|> m2 = PcAct $ \s -> [(m1, s), (m2, s)]
    empty = PcAct $ \s -> []
    many m = some m <|> pure []
    some m = (:) <$> m <*> many m

instance MonadPlus (PC c)

instance Semigroup (PC c a) where
    (<>) = (<|>)

instance Monoid (PC c a) where
    mempty = empty

instance MonadFail (PC c) where
    fail _ = empty

instance Failable (PC c a) where
    alt m1 m2 = PcAct $ map (uncurry $ (,) . PcVal) . (evalPC m1 /> evalPC m2)

instance FailableZero (PC c a) where
    nil = PcAct nil

instance Applicative (BP c) where
    pure = returnBP
    (<*>) = ap

instance Monad (BP c) where
    (>>=) = bindBP

instance Alternative (BP c) where
    m1 <|> m2 = BP $ pure (++) <*> runBP m1 <*> runBP m2
    empty = BP $ pure []
    many m = some m <|> pure []
    some m = (:) <$> m <*> many m

instance MonadPlus (BP c)

instance Failable (BP c a) where
    alt m1 m2 = BP $ pure (/>) <*> runBP m1 <*> runBP m2

instance FailableZero (BP c a) where
    nil = BP $ pure nil

instance Semigroup (BP c a) where
    (<>) = (<|>)

instance Monoid (BP c a) where
    mempty = empty
