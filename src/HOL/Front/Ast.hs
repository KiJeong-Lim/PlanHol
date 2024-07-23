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
charset:
    $small_letter = 'a'-'z'
    $big_letter = 'A'-'Z'
    $digit = '0'-'9'
regex:
    $Char = [. \ '\n' \ '\\' \ '\"'] + "\\n" + "\\\\" + "\\\"" + "\\\'" + "\\t"
    $SmallId = [$small_letter] [$small_letter $digit '_' $big_letter]*
    $LargeId = [$big_letter] [$small_letter $digit '_' $big_letter]*
main:
    $SmallId ==> <SMALL-ID>
    $LargeId ==> <LARGE-ID>
    ($LargeId ".")* / [$small_letter $big_letter] ==> <MODULE-QUAL>
-}

{- SYNTAX
type:
    <TYPE> ::=
        | <TYPE-VARIABLE>    -- type variable
        | <TYPE-CONSTANT>    -- type constant
        | <TYPE> <TYPE>      -- type application
        | <TYPE> "->" <TYPE> -- arrow
        | "list"             -- list type
        | "nat"              -- natural type
        | "char"             -- character type
        | "string"           -- list char
        | "o"                -- propositon type
        | <MACRO>            -- macro
term:
    <VARIABLE> ::=
        | <LARGE-ID> -- bounded variable (1)
        | <SMALL-ID> -- bounded variable (2)
    <CONSTANT-IDENTIFIER> ::=
        | <MODULE-QUAL> <SMALL-ID> -- qualified constant identifier
        | <SMALL-ID>               -- unqualified constant identifier
    <TERM> ::=
        | "_"                            -- wildcard
        | <LARGE-ID>                     -- meta-variable
        | <VARIABLE>                     -- variable
        | <TERM> <TERM>                  -- application
        | <VARIABLE> "\\" <TERM>         -- lambda abstraction
        | <CONSTANT-IDENTIFIER>          -- constant identifier
        | <PREFIX-CONSTANT> <TERM>       -- prefix operator
        | <TERM> <SUFFIX-CONSTANT>       -- suffix operator
        | <TERM> <INFIX-CONSTANT> <TERM> -- infix operator
        | <TERM> ":" <TYPE>              -- type annotation
        | <NAT-LITERAL>                  -- natural number
        | <SUC-LITERAL>                  -- successor
        | <TERM> <PLUS> <TERM>           -- addition
        | <NIL>                          -- empty list
        | <TERM> <CONS> <TERM>           -- list head
        | <TERM> <APP-LITERAL> <TERM>    -- concatenation
        | <TABULAR-FORM>                 -- tabular form
        | <CHAR-LITERAL>                 -- character literal
        | <STRING-LITERAL>               -- string literal
        | <MACRO>                        -- macro
formula:
    <ATOMIC-FORMULA> ::= <TERM>
    <RIGID-ATOMIC-FORMULA> ::= <TERM>
    <CLAUSE> ::=
        | <GOAL> "=>" <CLAUSE>                              -- if goal holds then clause holds
        | <CLAUSE> ":-" <GOAL>                              -- clause holds if goal holds
        | <CLAUSE> ":-" <GOAL> "with" <CONSTRAINT>          -- clause holds if goal holds whenever constraint is satisfied 
        | <CLAUSE> ":-" <GOAL> "with" "{" <CONSTRAINTS> "}" -- clause holds if goal holds whenever constraints are satisfied 
        | <CLAUSE> "&" <CLAUSE>                             -- both hold
        | <RIGID-ATOMIC-FORMULA>                            -- rigid atomic formula
    <GOAL> ::=
        | <ATOMIC-FORMULA>     -- atomic formula
        | <CLAUSE> "=>" <GOAL> -- implication
        | <GOAL> "," <GOAL>    -- conjunction
        | <GOAL> "&" <GOAL>    -- conjunction
        | <GOAL> ";" <GOAL>    -- disjunction
        | "pi" <TERM>          -- universal quantifier
        | "sigma" <TERM>       -- existential quantifier
        | "true"               -- top
        | "fail"               -- bottom
        | "!"                  -- cut operator
        | <TERM> "=" <TERM>    -- unifying operator
        | <TERM> ":=" <TERM>   -- evaluation operator
        | <MACRO>              -- macro
    <CONSTRAINT> ::=
        | <TERM> "=" <TERM>            -- identity constraint
        | <TERM> "=<" <TERM>           -- le constraint
        | <TERM> ">" <TERM>            -- gt constraint
        | <NOT> <RIGID-ATOMIC-FORMULA> -- not constraint
        | <RIGID-ATOMIC-FORMULA>       -- custom constraint
        | <MACRO>                      -- macro
    <CONSTRAINTS> ::=
        | <CONSTRAINT>                   -- single constraint
        | <CONSTRAINT> "," <CONSTARINTS> -- multiple constraint
toplevel:
    <CUSTOM-OPERATOR-FIXITY-DECL> ::=
        | "prefix" <CUSTOM-SYMBOL> <NAT-LITERAL>  -- prefix operator decl
        | "prefixr" <CUSTOM-SYMBOL> <NAT-LITERAL> -- prefixr operator decl
        | "infix" <CUSTOM-SYMBOL> <NAT-LITERAL>   -- infix operator decl
        | "infixl" <CUSTOM-SYMBOL> <NAT-LITERAL>  -- infixl operator decl
        | "infixr" <CUSTOM-SYMBOL> <NAT-LITERAL>  -- infixr operator decl
        | "suffix" <CUSTOM-SYMBOL> <NAT-LITERAL>  -- suffix operator decl
        | "suffixl" <CUSTOM-SYMBOL> <NAT-LITERAL> -- suffixl operator decl
    <TYPE-DECL> ::= <CONSTANT> ":" <TYPE> "."
    <TYPE-DEFN> ::=
        | "type" <TYPE-CON> ... ":=" <TYPE> "."        -- type synonym
        | "data" <TYPE-CON> ... ":=" ... "."           -- sum type
        | "data" <TYPE-CON> ... "where" ... "end."     -- gadt
        | "record" <TYPE-CON> ... ":=" "{" ... "}" "." -- record type
    <CONSTRAINT-INSTANCE> ::= "instance" ... "where" <RULE>* "end."
    <CONSTRAINT-CLASS-DECL> ::= "class" ... "where" ... "end."
    <TOPLEVEL-STMT> ::=
        | <ATTRIBUTE> <CUSTOM-OPERATOR-FIXITY-DECL>
        | <ATTRIBUTE> <TYPE-DECL>
        | <ATTRIBUTE> <TYPE-DEFN>
        | <ATTRIBUTE> <CONSTRAINT-INSTANCE>
        | <ATTRIBUTE> <CONSTRAINT-CLASS-DECL>
        | <ATTRIBUTE> <CLAUSE> "."
module:
    <MODULE-NAME> ::= <MODULE-QUAL> <LARGE-ID>
    <MODULE-HEADER> ::= "module" <MODULE-NAME> "."
    <IMPORT-DECL> ::= "import" <MODULE-NAME> "."
main:
    <MODULE> ::= <MODULE-HEADER> <IMPORT-DECL>* <TOP-LEVEL-STMT>*
    <QUERY> ::= <GOAL> "."
-}
