module ALPHA2.Header where

import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.State.Strict
import Data.Functor.Identity
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Z.Utils

type SPos = (Int, Int)

type LargeId = String

type SmallId = String

type Keyword = String

type MetaTVar = Unique

type IVar = Unique

type KindEnv = Map.Map TypeConstructor KindExpr

type TypeEnv = Map.Map DataConstructor PolyType

data SLoc
    = SLoc
        { _BegPos :: SPos
        , _EndPos :: SPos
        }
    deriving (Eq, Ord)

data Literal
    = NatL Integer
    | ChrL Char
    | StrL String
    deriving (Eq, Ord)

data LogicalOperator
    = LO_ty_pi
    | LO_if
    | LO_true
    | LO_fail
    | LO_cut
    | LO_and
    | LO_or
    | LO_imply
    | LO_pi
    | LO_sigma
    | LO_debug
    | LO_is
    deriving (Eq, Ord)

data DataConstructor
    = DC_LO LogicalOperator
    | DC_Named SmallId
    | DC_Unique Unique
    | DC_Nil
    | DC_Cons
    | DC_ChrL Char
    | DC_NatL Integer
    | DC_Succ
    | DC_eq
    | DC_le
    | DC_lt
    | DC_ge
    | DC_gt
    | DC_plus
    | DC_minus
    | DC_mul
    | DC_div
    deriving (Eq, Ord)

data TypeConstructor
    = TC_Arrow
    | TC_Named SmallId
    | TC_Unique Unique
    deriving (Eq, Ord)

data KindExpr
    = Star
    | KArr KindExpr KindExpr
    deriving (Eq)

data TCon
    = TCon TypeConstructor KindExpr
    deriving ()

data MonoType tvar
    = TyVar tvar
    | TyCon TCon
    | TyApp (MonoType tvar) (MonoType tvar)
    | TyMTV MetaTVar
    deriving (Eq)

data PolyType
    = Forall [SmallId] (MonoType Int)
    deriving ()

data TermExpr dcon annot
    = Var annot IVar
    | Con annot dcon 
    | App annot (TermExpr dcon annot) (TermExpr dcon annot)
    | Lam annot IVar (TermExpr dcon annot)
    deriving ()

data Program term
    = Program
        { moduleName :: String
        , _KindDecls :: KindEnv
        , _TypeDecls :: TypeEnv
        , _FactDecls :: [term]
        }
    deriving ()

class HasSLoc a where
    getSLoc :: a -> SLoc

instance Semigroup SLoc where
    SLoc pos1 pos2 <> SLoc pos1' pos2' = SLoc (min pos1 pos1') (max pos2 pos2')

instance Show SLoc where
    showsPrec _ = const id

instance Outputable SLoc where
    pprint _ (SLoc (row1, col1) (row2, col2)) = strcat
        [ showsPrec 0 row1
        , strstr ":"
        , showsPrec 0 col1
        , strstr "-"
        , showsPrec 0 row2
        , strstr ":"
        , showsPrec 0 col2
        ]

instance Show LogicalOperator where
    showsPrec _ logical_operator = case logical_operator of
        LO_ty_pi -> strstr "Lambda"
        LO_if -> strstr ":-"
        LO_true -> strstr "true"
        LO_fail -> strstr "fail"
        LO_is -> strstr "is"
        LO_cut -> strstr "!"
        LO_and -> strstr ","
        LO_or -> strstr ";"
        LO_imply -> strstr "=>"
        LO_pi -> strstr "pi"
        LO_sigma -> strstr "sigma"
        LO_debug -> strstr "debug"

instance Show DataConstructor where
    showsPrec _ data_constructor = case data_constructor of
        DC_LO logical_operator -> showsPrec 0 logical_operator
        DC_Named name -> strstr name
        DC_Unique unique -> showsPrec 0 (unUnique unique)
        DC_Nil -> strstr "[]"
        DC_Cons -> strstr "::"
        DC_ChrL chr -> showsPrec 0 chr
        DC_NatL nat -> showsPrec 0 nat
        DC_Succ -> strstr "s"
        DC_eq -> strstr "="

instance Show TypeConstructor where
    showsPrec _ type_constructor = case type_constructor of
        TC_Arrow -> strstr "->"
        TC_Named name -> strstr name
        TC_Unique unique -> showsPrec 0 (unUnique unique)

instance Read KindExpr where
    readsPrec 0 str0 = [ (kin1 `KArr` kin2, str2) | (kin1, ' ' : '-' : '>' : ' ' : str1) <- readsPrec 1 str0, (kin2, str2) <- readsPrec 0 str1 ] ++ readsPrec 1 str0
    readsPrec 1 ('*' : str0) = [(Star, str0)]
    readsPrec 1 ('(' : str0) = [ (kin, str1) | (kin, ')' : str1) <- readsPrec 0 str0 ]
    readList = undefined

instance Outputable KindExpr where
    pprint 0 (kin1 `KArr` kin2) = pprint 1 kin1 . strstr " -> " . pprint 0 kin2
    pprint 0 kin1 = pprint 1 kin1
    pprint 1 Star = strstr "type"
    pprint 1 kin1 = pprint 2 kin1
    pprint _ kin1 = strstr "(" . pprint 0 kin1 . strstr ")"

instance Eq TCon where
    TCon type_constructor_1 _ == TCon type_constructor_2 _ = type_constructor_1 == type_constructor_2

instance Ord TCon where
    TCon type_constructor_1 _ `compare` TCon type_constructor_2 _ = type_constructor_1 `compare` type_constructor_2

instance Outputable TCon where
    pprint _ (TCon type_constructor _) = showsPrec 0 type_constructor

instance HasAnnot (TermExpr dcon) where
    getAnnot (Var annot _) = annot
    getAnnot (Con annot _) = annot
    getAnnot (App annot _ _) = annot
    getAnnot (Lam annot _ _) = annot
    setAnnot annot (Var _ x) = Var annot x
    setAnnot annot (Con _ c) = Con annot c
    setAnnot annot (App _ t1 t2) = App annot t1 t2
    setAnnot annot (Lam _ x t1) = Lam annot x t1

mkTyList :: MonoType tvar -> MonoType tvar
mkTyList typ1 = TyApp (TyCon (TCon (TC_Named "list") (read "* -> *"))) typ1

mkTyChr :: MonoType tvar
mkTyChr = TyCon (TCon (TC_Named "char") (read "*"))

mkTyNat :: MonoType tvar
mkTyNat = TyCon (TCon (TC_Named "nat") (read "*"))

mkTyO :: MonoType tvar
mkTyO = TyCon (TCon (TC_Named "o") (read "*"))

mkTyArrow :: MonoType tvar -> MonoType tvar -> MonoType tvar
typ1 `mkTyArrow` typ2 = TyApp (TyApp (TyCon (TCon TC_Arrow (read "* -> * -> *"))) typ1) typ2
