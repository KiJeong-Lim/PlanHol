module TEST.Term2 where

import Z.Utils

{- My Goals are:
[1] Handle meta-variable with local context and cell with meta-context. <--- (???)
[2] Also print names of all variables in a cell.
[3] And being able to handle the definiton (i.e., allow delta-reduction)
========================================================================

-}

data ReductionOption
    = WHNF
    | HNF
    | NF
    deriving (Eq, Show)

data Name
    = Name String Unique
    deriving (Eq, Show)

{- [1st try...]

type DeBruijnIndex = Int

type Name = String -- small letter

type Constructor = String -- capital letter

type MetaVar = String -- "?" + small letter

type Nat_ol = Int

type Nat_nl = Int

type Nat_l = Int

type GlobalEnv = [GlobalEnvItem]

data TermNode
    = NVar Name DeBruijnIndex
    | NFun Name
    | NCon Constructor
    | NApp TermNode TermNode
    | NLam Name TermNode
    | NLet Name TermNode TermNode
    | NMat TermNode [(Constructor, TermNode)]
    | NFix Int [(Name, TermNode)]
    | Susp TermNode LocalCtx
    | NQue MetaVar [TermNode]
    deriving (Eq, Show)

data LocalCtx
    = LocalCtx { _local_ol :: Nat_ol, _local_nl :: Nat_nl, _local_env :: [LocalCtxItem] }
    deriving (Eq, Show)

data LocalCtxItem
    = DummyL Name Nat_l
    | BindsL Name TermNode Nat_l
    deriving (Eq, Show)

data MetaCtx
    = MetaCtx { _meta_ol :: Nat_ol, _meta_nl :: Nat_nl, _meta_env :: [MetaCtxItem] }
    deriving (Eq, Show)

data MetaCtxItem
    = DummyM MetaVar [LocalCtx]
    | BindsM MetaVar TermNode [LocalCtx]
    deriving (Eq, Show)

data GlobalEnvItem
    = FunDefn Name TermNode
    deriving (Eq, Show)

reduce :: TermNode -> LocalCtx -> MetaCtx -> GlobalEnv -> ReductionOption -> TermNode
reduce = undefined

-}
