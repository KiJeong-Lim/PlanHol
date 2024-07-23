module HOL.Front.Ast where

import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.State.Strict
import Control.Monad.Trans.Reader
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Z.Utils

{-
[[LEXEME]]

$small_letter = 'a'-'z'
$big_letter = 'A'-'Z'
$digit = '0'-'9'
$Char = [. \ '\n' \ '\\' \ '\"'] + "\\n" + "\\\\" + "\\\"" + "\\\'" + "\\t"
$SmallId = [$small_letter] [$small_letter $digit '_' $big_letter]*
$LargeId = [$big_letter] [$small_letter $digit '_' $big_letter]* + "_"

main:
    $SmallId ==> <SMALL-ID>
    $LargeId ==> <LARGE-ID>
    ($LargeId ".")* / [$small_letter $big_letter] ==> <MODULE-QUAL>

[[SYNTAX]]

<MODULE-HEADER> ::=
    | "module" <MODULE-NAME> "."
<IMPORT-DECL> ::=
    | "import" <MODULE-NAME> "."
<TOP-LEVEL-STMT> ::=
    | <CUSTOM-OPERATOR-FIXITY-DECL>
    | <DATA-TYPE-DEFN>
    | <TYPE-DECL>
    | <CLAUSE>
<MODULE-NAME> ::=
    | <MODULE-QUAL> <LARGE-ID>
<VARIABLE> ::=
    | <LARGE-ID> -- meta-variable
    | <LARGE-ID> -- bounded variable (1)
    | <SMALL-ID> -- bounded variable (2)
<CONSTANT-IDENTIFIER> ::=
    | <MODULE-QUAL> <SMALL-ID> -- qualified constant identifier
    | <SMALL-ID>               -- unqualified constant identifier

main:
    <MODULE> ::=
        | <MODULE-HEADER> <IMPORT-DECL>* <TOP-LEVEL-STMT>*
    <QUERY> ::=
        | <GOAL> "."
-}
