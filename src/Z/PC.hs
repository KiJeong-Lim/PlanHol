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
