module HOL.Front.Ast where

import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.State.Strict
import Control.Monad.Trans.Reader
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Z.Utils

{- LEXEME
others:
    $small_letter = 'a'-'z'
    $big_letter = 'A'-'Z'
    $digit = '0'-'9'
    $Char = [. \ '\n' \ '\\' \ '\"'] + "\\n" + "\\\\" + "\\\"" + "\\\'" + "\\t"
    $SmallId = [$small_letter] [$small_letter $digit '_' $big_letter]*
    $LargeId = [$big_letter] [$small_letter $digit '_' $big_letter]*
main:
    $SmallId ==> <SMALL-ID>
    $LargeId ==> <LARGE-ID>
    ($LargeId ".")* / [$small_letter $big_letter] ==> <MODULE-QUAL>
-}

{- SYNTAX
others:
    <VARIABLE> ::=
        | <LARGE-ID> -- meta-variable
        | <LARGE-ID> -- bounded variable (1)
        | <SMALL-ID> -- bounded variable (2)
    <CONSTANT-IDENTIFIER> ::=
        | <MODULE-QUAL> <SMALL-ID> -- qualified constant identifier
        | <SMALL-ID>               -- unqualified constant identifier
    <TERM> ::=
        | "_"                            -- wildcard
        | <VARIABLE>                     -- variable
        | <TERM> <TERM>                  -- application
        | "\\" <TERM>                    -- lambda abstraction
        | <CONSTANT-IDENTIFIER>          -- constant identifier
        | <PREFIX-CONSTANT> <TERM>       -- prefix operator
        | <TERM> <SUFFIX-CONSTANT>       -- suffix operator
        | <TERM> <INFIX-CONSTANT> <TERM> -- infix operator
    <MODULE-NAME> ::=
        | <MODULE-QUAL> <LARGE-ID>
    <MODULE-HEADER> ::=
        | "module" <MODULE-NAME> "."
    <IMPORT-DECL> ::=
        | "import" <MODULE-NAME> "."
    <TOP-LEVEL-STMT> ::=
        | <CUSTOM-OPERATOR-FIXITY-DECL>
        | <DATA-TYPE-DEFN>
        | <TYPE-DECL>
        | <CLAUSE>
main:
    <MODULE> ::=
        | <MODULE-HEADER> <IMPORT-DECL>* <TOP-LEVEL-STMT>*
    <QUERY> ::=
        | <GOAL> "."
-}
