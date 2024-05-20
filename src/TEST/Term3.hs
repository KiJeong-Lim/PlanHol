module TEST.Term3 where

import Z.Utils

type VarName = Nat

type CtrName = String

type MVarName = String

data Term
    = Var (VarName)
    | Ctr (CtrName)
    | App (Term) (Term)
    | Lam (VarName) (Term) 
    | Mat (Term) [((CtrName, [VarName]), Term)]
    | Fix (VarName) (Term)
    | Fun (VarName)
    | Meta (MVarName) [Term]
    deriving (Eq, Ord, Show)
