module SystemF where

import Prelude

data Typ where
    TyAll : (Typ -> Typ) -> Typ
    TyArr : Typ -> Typ -> Typ
    deriving (Copy)

data Trm where
    App : Trm -> Trm -> Trm
    Lam : (Trm -> Trm) -> Trm
    TApp : Trm -> Typ -> Trm
    TLam : (Typ -> Trm) -> Trm
    deriving (Copy)
