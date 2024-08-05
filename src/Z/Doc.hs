module Z.Doc where

import System.Console.Pretty
import Z.Algorithms
import Z.Utils

data Doc
    = DT Int Int (List [(Char, (Maybe Style, Maybe Color))])
    | DB !Char (Maybe Style, Maybe Color)
    | DV !Doc !Doc
    | DH !Doc !Doc
    deriving ()

mkDT :: List [(Char, (Maybe Style, Maybe Color))] -> Doc
mkDT ss = DT (maximum (0 : map length ss)) (length ss) ss

text :: String -> Doc
text "" = mkDT []
text ss = mkDT [ map (\c -> (c, (Nothing, Nothing))) s | s <- lines ss ]

textit :: String -> Doc
textit "" = mkDT []
textit ss = mkDT [ map (\c -> (c, (Just Italic, Nothing))) s | s <- lines ss ]

textbf :: String -> Doc
textbf "" = mkDT []
textbf ss = mkDT [ map (\c -> (c, (Just Bold, Nothing))) s | s <- lines ss ]

red :: Doc -> Doc
red (DT row col ls) = DT row col [ map (uncurry $ \c -> uncurry $ \sty -> \clr -> (c, (sty, clr /> Just Red))) l | l <- ls ]
red (DB c (sty, clr)) = DB c (sty, clr /> Just Red)
red (DV d1 d2) = DV (red d1) (red d2)
red (DH d1 d2) = DH (red d1) (red d2)

blue :: Doc -> Doc
blue (DT row col ls) = DT row col [ map (uncurry $ \c -> uncurry $ \sty -> \clr -> (c, (sty, clr /> Just Blue))) l | l <- ls ]
blue (DB c (sty, clr)) = DB c (sty, clr /> Just Blue)
blue (DV d1 d2) = DV (blue d1) (blue d2)
blue (DH d1 d2) = DH (blue d1) (blue d2)

vcat :: [Doc] -> Doc
vcat [] = text ""
vcat [d] = d
vcat (d : ds) = DV d (vcat ds)

hcat :: [Doc] -> Doc
hcat [] = mempty
hcat [d] = d
hcat (d : ds) = d <> hcat ds

ptext :: Outputable a => a -> Doc
ptext = text . pshow

beam :: Char -> Doc
beam c = DB c (Just Bold, Nothing)

renderDoc :: Doc -> String
renderDoc = makeUp . mkBoard where
    mkBoard :: Doc -> List [(Char, (Maybe Style, Maybe Color))]
    mkBoard = linesFromVField . normalizeV where
        getMaxHeight :: [Doc] -> Int
        getMaxHeight ds = maximum (0 : [ col | DT row col ls <- ds ])
        getMaxWidth :: [Doc] -> Int
        getMaxWidth ds = maximum (0 : [ row | DT row col ls <- ds ])
        expandHeight :: Int -> Doc -> Doc
        expandHeight col (DB c info) = DT 1 col [ map (\c -> (c, info)) l | l <- replicate col [c] ]
        expandHeight col (DT row col' field) = DT row col (field ++ replicate (col - col') (replicate row (' ', (Nothing, Nothing))))
        expandWidth :: Int -> Doc -> Doc
        expandWidth row (DB c info) = DT row 1 [replicate row (c, info)]
        expandWidth row (DT row' col field) = DT row col [ str ++ replicate (row - row') (' ', (Nothing, Nothing)) | str <- field ]
        horizontal :: Doc -> [Doc]
        horizontal (DB c info) = [DB c info]
        horizontal (DT row col field) = [DT row col field]
        horizontal (DV v1 v2) = [normalizeV (DV v1 v2)]
        horizontal (DH v1 v2) = horizontal v1 ++ horizontal v2
        vertical :: Doc -> [Doc]
        vertical (DB c info) = [DB c info]
        vertical (DT row col field) = [DT row col field]
        vertical (DH v1 v2) = return (normalizeH (DH v1 v2))
        vertical (DV v1 v2) = vertical v1 ++ vertical v2
        hsum :: Int -> [Doc] -> Doc
        hsum col [] = DT 0 col (replicate col [])
        hsum col (v : vs) = case (v, hsum col vs) of
            (DT row1 _ field1, DT row2 _ field2) -> DT (row1 + row2) col (zipWith (++) field1 field2)
        vsum :: Int -> [Doc] -> Doc
        vsum row [] = DT row 0 []
        vsum row (v : vs) = case (v, vsum row vs) of
            (DT _ col1 field1, DT _ col2 field2) -> DT row (col1 + col2) (field1 ++ field2)
        normalizeH :: Doc -> Doc
        normalizeH = merge . concat . map horizontal . flatten where
            flatten :: Doc -> [Doc]
            flatten (DH v1 v2) = flatten v1 ++ flatten v2
            flatten v1 = [v1]
            merge :: [Doc] -> Doc
            merge vs = hsum (getMaxHeight vs) (map (expandHeight (getMaxHeight vs)) vs)
        normalizeV :: Doc -> Doc
        normalizeV = merge . concat . map vertical . flatten where
            flatten :: Doc -> [Doc]
            flatten (DV v1 v2) = flatten v1 ++ flatten v2
            flatten v1 = [v1]
            merge :: [Doc] -> Doc
            merge vs = vsum (getMaxWidth vs) (map (expandWidth (getMaxWidth vs)) vs)
        linesFromVField :: Doc -> List [(Char, (Maybe Style, Maybe Color))]
        linesFromVField (DT row col field) = field
    makeUp :: List [(Char, (Maybe Style, Maybe Color))] -> String
    makeUp ls = unlines [ l >>= beautify | l <- ls ] where
        beautify :: (Char, (Maybe Style, Maybe Color)) -> String
        beautify (c, (Nothing, Nothing)) = [c]
        beautify (c, (Just sty, Nothing)) = style sty [c]
        beautify (c, (Nothing, Just clr)) = color clr [c]
        beautify (c, (Just sty, Just clr)) = color clr (style sty [c])

instance Semigroup Doc where
    d1 <> d2 = DH d1 d2

instance Monoid Doc where
    mempty = DT 0 0 []
