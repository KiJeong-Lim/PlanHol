module ALPHA1.Grammar where

import ALPHA1.Ast
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
        | <CLAUSE> ":-" <GOAL>                              -- clause holds if goal holds
        | <CLAUSE> ":-" <GOAL> "with" <CONSTRAINT>          -- clause holds if goal holds whenever constraint is satisfied 
        | <CLAUSE> ":-" <GOAL> "with" "{" <CONSTRAINTS> "}" -- clause holds if goal holds whenever constraints are satisfied 
        | <CLAUSE> "&" <CLAUSE>                             -- conjunction
        | "pi" <CLAUSE>                                     -- universal quantifier
        | <RIGID-ATOMIC-FORMULA>                            -- rigid atomic formula
    <GOAL> ::=
        | <ATOMIC-FORMULA>     -- atomic formula
        | <GOAL> ":-" <CLAUSE> -- implication
        | <GOAL> "," <GOAL>    -- conjunction
        | <GOAL> ";" <GOAL>    -- disjunction
        | "pi" <GOAL>          -- universal quantifier
        | "sigma" <GOAL>       -- existential quantifier
        | "true"               -- top
        | "fail"               -- bottom
        | "!"                  -- cut operator
        | <TERM> "=" <TERM>    -- unifying operator
        | <TERM> ":=" <TERM>   -- evaluation operator
        | "debug"              -- debug
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
        | "prefix" <NAT-LITERAL> <CUSTOM-SYMBOL>  -- prefix operator decl
        | "prefixr" <NAT-LITERAL> <CUSTOM-SYMBOL> -- prefixr operator decl
        | "infix" <NAT-LITERAL> <CUSTOM-SYMBOL>   -- infix operator decl
        | "infixl" <NAT-LITERAL> <CUSTOM-SYMBOL>  -- infixl operator decl
        | "infixr" <NAT-LITERAL> <CUSTOM-SYMBOL>  -- infixr operator decl
        | "suffix" <NAT-LITERAL> <CUSTOM-SYMBOL>  -- suffix operator decl
        | "suffixl" <NAT-LITERAL> <CUSTOM-SYMBOL> -- suffixl operator decl
    <TYPE-DECL> ::= "type" <CONSTANT> ":" <TYPE> "."
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
    <IMPORT-DECL> ::=
        | <ATTRIBUTE> "import" <MODULE-NAME> <AS-SHORT-CUT> "."
        | <ATTRIBUTE> "import" <MODULE-NAME> "qualified" <AS-SHORT-CUT> "."
    <AS-SHORT-CUT> ::=
        | "as" <MODULE-NAME>
        |
main:
    <MODULE> ::= <MODULE-HEADER> <IMPORT-DECL>* <TOP-LEVEL-STMT>*
    <QUERY> ::=
        | <GOAL> "."
        | "import" <MODULE-NAME> "."
-}
