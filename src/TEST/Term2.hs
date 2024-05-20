module TEST.Term2 where

import Z.Utils

{- My Goals are:
[1] Handle meta-variable with local context and cell with meta-context. <--- (???)
[2] Also print names of all variables in a cell.
[3] And being able to handle the definiton (i.e., allow delta-reduction)
========================================================================
-}

type DeBruijnIndex = Int

type DataConstructorName = String

type IndividualVariableName = String

type MetaVariableName = String

type ReferenceName = String

type SuspensionEnv = [SuspensionEnvItem]

type Nat_ol = Nat

type Nat_nl = Nat

data ReductionOption
    = WHNF
    | HNF
    | NF
    deriving (Eq, Show)

data Identifier name
    = Identifier { nameOf :: name }
    deriving (Eq, Ord, Show)

data TermNode
    = NIdx (DeBruijnIndex)
    | NCtr (Identifier DataConstructorName)
    | NApp (TermNode) (TermNode)
    | NLam (TermNode)
    | NFun (Identifier ReferenceName)
    | Meta (Identifier MetaVariableName) [TermNode]
    | Susp (TermNode) (Suspension)
    deriving (Eq, Ord, Show)

data SuspensionEnvItem
    = Dummy Int
    | Binds TermNode Int
    deriving (Eq, Ord, Show)

data Suspension
    = Suspension { _susp_ol :: Nat_ol, _susp_nl :: Nat_nl, _susp_env :: SuspensionEnv }
    deriving (Eq, Ord, Show)

mkNIdx :: DeBruijnIndex -> TermNode
mkNIdx i = if i >= 0 then NIdx i else error "***mkNIdx: A negative De-Bruijn index given..."

mkNCtr :: Identifier DataConstructorName -> TermNode
mkNCtr c = NCtr $! c

mkNApp :: TermNode -> TermNode -> TermNode
mkNApp t1 t2 = (NApp $! t1) $! t2

mkNLam :: TermNode -> TermNode
mkNLam t1 = NLam $! t1

mkNFun :: Identifier ReferenceName -> TermNode
mkNFun f = NFun $! f

mkMeta :: Identifier MetaVariableName -> [TermNode] -> TermNode
mkMeta x ts = (Meta $! x) $! ts

mkSusp :: TermNode -> Suspension -> TermNode
mkSusp t susp
    | NCtr {} <- t = t
    | Suspension ol nl env <- susp = if ol == 0 && nl == 0 then t else env `seq` Susp t susp

buildSusp :: TermNode -> Nat_ol -> Nat_nl -> SuspensionEnv -> TermNode
buildSusp t ol nl env = mkSusp t (mkSuspension ol nl env)

addDummy :: Nat -> SuspensionEnv -> SuspensionEnv
addDummy l env = l `seq` Dummy l : env

addBinds :: TermNode -> Nat -> SuspensionEnv -> SuspensionEnv
addBinds t l env = t `seq` l `seq` Binds t l : env

emptySuspensionEnv :: SuspensionEnv
emptySuspensionEnv = []

nilSuspension :: Suspension
nilSuspension = Suspension 0 0 []

mkSuspension :: Nat_ol -> Nat_nl -> SuspensionEnv -> Suspension
mkSuspension ol nl env
    | ol == length env && nl >= 0 = Suspension ol nl env 
    | otherwise = error "***mkSuspension: ol /= length env..."

rewriteWithSusp :: TermNode -> Suspension -> ReductionOption -> TermNode
rewriteWithSusp t susp option = dispatch t where
    ol :: Nat_ol
    ol = _susp_ol susp
    nl :: Nat_nl
    nl = _susp_nl susp
    env :: SuspensionEnv
    env = _susp_env susp
    dispatch :: TermNode -> TermNode
    dispatch (NIdx i)
        | i >= ol = mkNIdx (i - ol + nl)
        | i >= 0 = case env !! i of
            Dummy l -> mkNIdx (nl - l)
            Binds t l -> rewriteWithSusp t (mkSuspension 0 (nl - l) []) option
        | otherwise = error "***rewriteWithSusp: A negative De-Bruijn index given..."
    dispatch (NApp t1 t2)
        = case t1' of
            NLam t11 -> beta t11
            _ -> reductionOption option
        where
            t1' :: TermNode
            t1' = rewriteWithSusp t1 susp WHNF
            beta :: TermNode -> TermNode
            beta (Susp t' (Suspension ol' nl' (Dummy l' : env')))
                | nl' == l' = rewriteWithSusp t' (mkSuspension ol' (pred nl') (addBinds (Susp t2 susp) (pred l') env')) option
            beta t' = rewriteWithSusp t (mkSuspension 1 0 (addBinds (buildSusp t2 ol nl env) 0 emptySuspensionEnv)) option
            reductionOption :: ReductionOption -> TermNode
            reductionOption NF = mkNApp (rewriteWithSusp t1' nilSuspension option) (rewriteWithSusp t2 susp option)
            reductionOption HNF = mkNApp (rewriteWithSusp t1' nilSuspension option) (Susp t2 susp)
            reductionOption WHNF = mkNApp t1' (Susp t2 susp)
    dispatch (NLam t1)
        | option == WHNF = Susp t1 susp'
        | otherwise = rewriteWithSusp t1 susp' option
        where
            susp' :: Suspension
            susp' = mkSuspension (succ ol) (succ nl) (addDummy (succ nl) env)
    dispatch (NFun f)
        = mkNFun f
    dispatch (Meta x ts)
        = mkMeta x (map (rewrite NF) ts)
    dispatch (Susp t' susp')
        | ol' == 0 && nl' == 0 = rewriteWithSusp t' susp option
        | ol == 0 = rewriteWithSusp t' (mkSuspension ol' (nl + nl') env') option
        | otherwise = go (rewriteWithSusp t' susp' option)
        where
            ol' :: Nat_ol
            ol' = _susp_ol susp'
            nl' :: Nat_nl
            nl' = _susp_nl susp'
            env' :: SuspensionEnv
            env' = _susp_env susp'
            go :: TermNode -> TermNode
            go (NLam t1)
                | option == WHNF = mkNLam (Susp t1 susp1)
                | otherwise = mkNLam (rewriteWithSusp t1 susp1 option)
                where
                    susp1 :: Suspension
                    susp1 = mkSuspension (succ ol') (succ nl') (addDummy (succ nl') env')
            go t = rewriteWithSusp t susp option
    dispatch t
        = mkSusp t susp

rewrite :: ReductionOption -> TermNode -> TermNode
rewrite option t = rewriteWithSusp t nilSuspension option

unfoldNApp :: TermNode -> (TermNode, [TermNode])
unfoldNApp = flip go [] where
    go :: TermNode -> [TermNode] -> (TermNode, [TermNode])
    go (NApp t1 t2) ts = go t1 (t2 : ts)
    go t ts = (t, ts)

instance Show name => Outputable (Identifier name) where
    pprint _ (Identifier { nameOf = name }) = shows name

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
