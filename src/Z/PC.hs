module Z.PC where

import Z.Utils

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

isInCharSet :: (Eq c, Enum c) => c -> CharSet c -> Bool
isInCharSet c (CsUniv) = True
isInCharSet c (CsPlus cs1 cs2) = isInCharSet c cs1 || isInCharSet c cs2
isInCharSet c (CsDiff cs1 cs2) = isInCharSet c cs1 && not (isInCharSet c cs2)
isInCharSet c (CsEnum c1 c2) = c `elem` [c1 .. c2]
isInCharSet c (CsAtom c1) = c == c1
