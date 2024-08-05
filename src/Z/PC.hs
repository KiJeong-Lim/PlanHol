{-# LANGUAGE DeriveFunctor #-}
module Z.PC where

import Control.Applicative
import Control.Monad
import Control.Monad.Fail
import Data.Function
import Data.Functor
import Data.List as List
import Z.Algorithms
import Z.Utils

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
    = LocChar { locOfLocChar :: (Int, Int), charOfLocChar :: Char }
    deriving (Show)

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

readCharSet :: String -> CharSet Char
readCharSet = go . map fst . runBP (parseCharSet 0 <* eof) where
    go :: [CharSet Char] -> CharSet Char
    go [] = error "readCharSet: no parse..."
    go (x : _) = x

readRegEx :: String -> RegEx Char
readRegEx = go . map fst . runBP (parseRegEx 0 <* eof) where
    go :: [RegEx Char] -> RegEx Char
    go [] = error "readRegEx: no parse..."
    go (x : _) = x

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

instance Eq LocChar where
    (==) = (==) `on` charOfLocChar

instance Ord LocChar where
    (<=) = (<=) `on` charOfLocChar
