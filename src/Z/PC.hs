module Z.PC where

import Control.Applicative
import Control.Monad
import Data.Function
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
mkReMult (ReWord s1) (ReWord s2) = ReWord $! s1 ++ s2
mkReMult (ReZero) re2 = mkReZero
mkReMult re1 (ReZero) = mkReZero
mkReMult re1 re2 = ReMult re1 re2

mkReStar :: RegEx c -> RegEx c
mkReStar (ReZero) = ReWord []
mkReStar (ReWord []) = ReWord []
mkReStar (ReStar re11) = mkReStar re11
mkReStar re1 = ReStar re1

isInCharSet :: (Eq c, Enum c) => c -> CharSet c -> Bool
isInCharSet c (CsUniv) = True
isInCharSet c (CsPlus cs1 cs2) = isInCharSet c cs1 || isInCharSet c cs2
isInCharSet c (CsDiff cs1 cs2) = isInCharSet c cs1 && not (isInCharSet c cs2)
isInCharSet c (CsEnum c1 c2) = c `elem` [c1 .. c2]
isInCharSet c (CsAtom c1) = c == c1

returnPC :: a -> PC c a
returnPC = PcVal

bindPC :: PC c a -> (a -> PC c a') -> PC c a'
bindPC (PcVal x) k = k x
bindPC (PcAct p) k = PcAct $ \s -> [ (bindPC m k, s') | (m, s') <- p s ]

evalPC :: PC c a -> List c -> [(a, List c)]
evalPC (PcVal x) = curry return x
evalPC (PcAct p) = uncurry evalPC <=< p

execPC :: PC c a -> List c -> Either (List c) a
execPC m s = do
    let findShortest = head . mSort ((<=) `on` length)
        loop (PcVal x) s = return [(x, s)]
        loop (PcAct p) s
            | null res = Left $! s
            | otherwise = if null oks then Left $! findShortest nos else return $! oks
            where
                res = [ loop m s' | (m, s') <- p s ]
                oks = [ (x, s'') | Right ok <- res, (x, s'') <- ok ]
                nos = [ s' | Left s' <- res ]
    res <- loop m s
    oks <- if null res then Left $! s else return $! [ x | (x, []) <- res ]
    case oks of
        [] -> Left $! findShortest (map snd res)
        x : _ -> return x

auto :: Read a => Prec -> PC Char a
auto prec = PcAct $ map (uncurry $ (,) . PcVal) . readsPrec prec

char :: (c -> Bool) -> PC c c
char cond = PcAct $ \s -> if null s then [] else let c = head s in if cond c then one (PcVal c, tail s) else []

consume :: Eq c => [c] -> PC c ()
consume prefix = PcAct $ \s -> let n = length prefix in if take n s == prefix then one (PcVal (), drop n s) else []

match :: Eq c => [c] -> PC c ()
match prefix = PcAct $ \s -> let n = length prefix in if take n s == prefix then one (PcVal (), s) else []

instance Applicative (PC c) where
    pure = returnPC
    (<*>) = ap

instance Monad (PC c) where
    (>>=) = bindPC

instance Alternative (PC c) where
    m1 <|> m2 = PcAct $ \s -> [(m1, s), (m2, s)]
    empty = PcAct $ \s -> []

instance MonadPlus (PC c)

instance Semigroup (PC c a) where
    (<>) = (<|>)

instance Monoid (PC c a) where
    mempty = empty
