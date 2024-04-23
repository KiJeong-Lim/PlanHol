module HOL.Front.Ast where

import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.State.Strict
import Control.Monad.Trans.Reader
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Z.Utils

{- SYNTAX

<< LEXER >>
$que ::= "?-"
$dot ::= "."
$comma ::= ","
$semicolon ::= ";"
$fatarrow ::= "=>"
$pi ::= "pi"
$sigma ::= "sigma"
$var ::= 
$uid ::= 
$lid ::= 
$con ::= $lid

<< PARSER >>
[module] MODULE ::= "module" $uid "where" IMPORT* STATEMENT*
[query] QUERY ::= "?-" G "."
[import_decl] IMPORT ::= "import"
[statement] STATEMET ::= D "." | FUNCDEFN | TYPEDECL | DATADEFN | CONSTRAINTDEFN

[goal] G ::= A | G "," G | G ";" G | D "=>" G | "pi" V "\" G | "sigma" V "\" G | "true" | "!" | "fail" | E
[rule] D ::= A | A ":-" G | "pi" V "\" D | D "&&" D
[atomic_formula] A ::= P T*
[head] H ::= V | C
[term] T ::= V "\" T | H T*
[goal_extension] E ::= T "=" T | T "is" T | G "with" "{" R* "}"
[constraint] R ::= M ";" | B ";" | ...
[mathematical_constraint] M ::= ...
[boolean_constraint] B ::= ...
[predicate] P ::= 
[constants] C ::= 
[variable] V ::= 

-}
