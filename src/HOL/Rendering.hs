module HOL.Rendering where

import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import HOL.Ast
import HOL.TermNode
import Z.Algorithms
import Z.Doc
import Z.Utils

data ViewNode
    = ViewIVar Int
    | ViewLVar LargeId
    | ViewDCon Name
    | ViewIApp ViewNode ViewNode
    | ViewILam Int ViewNode
    | ViewTVar LargeId
    | ViewTCon Name
    | ViewTApp ViewNode ViewNode
    | ViewOper (Fixity ViewNode, Prec)
    | ViewNatL Integer
    | ViewChrL Char
    | ViewStrL String
    | ViewList [ViewNode]
    deriving (Eq, Ord, Show)

{-
preludeMacroDefs :: Map.Map Name MacroDef
preludeMacroDefs = Map.fromList
    [ (QualifiedName preludeModule "string", ([], "(std.prelude.list std.prelude.char)"))
    , (QualifiedName preludeModule " is ", (["$LHS", "$RHS"], "$LHS std.prelude.:= $RHS"))
    ]
-}

renderTermNode :: Module () -> TermNode -> Doc
renderTermNode env = undefined -- renderViewNode . writeShortName . foldMacro . mkViewNode . writeFullName
