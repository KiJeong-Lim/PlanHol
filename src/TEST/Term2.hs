module TEST.Term2 where

import Z.Utils

{- Goals are:
[1] Handle meta-variable with local context and cell with meta-context.
    ==> This is meaningless.
[2] Also print names of all variables in a cell.
[3] And being able to handle the definiton (i.e., allow delta-reduction).
=========================================================================
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
    = Identifier { nameOf :: !(name) }
    deriving (Eq, Ord, Show)

data TermNode
    = NIdx (DeBruijnIndex)
    | NCtr (Identifier DataConstructorName)
    | NApp (TermNode) (TermNode)
    | NLam (TermNode)
    | NFun (Identifier ReferenceName)
    | Meta (Identifier MetaVariableName)
    | Susp (TermNode) (Suspension)
    deriving (Eq, Ord, Show)

data SuspensionEnvItem
    = Dummy (Int)
    | Binds (TermNode) (Int)
    deriving (Eq, Ord, Show)

data Suspension
    = Suspension { _susp_ol :: Nat_ol, _susp_nl :: Nat_nl, _susp_env :: SuspensionEnv }
    deriving (Eq, Ord, Show)

unfoldNApp :: TermNode -> (TermNode, [TermNode])
unfoldNApp = flip go [] where
    go :: TermNode -> [TermNode] -> (TermNode, [TermNode])
    go (NApp t1 t2) ts = go t1 (t2 : ts)
    go t ts = (t, ts)
{-# INLINEABLE unfoldNApp #-}

normalize :: ReductionOption -> TermNode -> TermNode
normalize option t = normalizeWithSuspension t nilSuspension option
{-# INLINABLE normalize #-}

normalizeWithSuspension :: TermNode -> Suspension -> ReductionOption -> TermNode
normalizeWithSuspension t susp option = dispatch t where
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
            Binds t' l -> normalizeWithSuspension t' (mkSuspension 0 (nl - l) []) option
        | otherwise = error "***normalizeWithSusp: A negative De-Bruijn index given..."
    dispatch (NCtr {})
        = t
    dispatch (NApp t1 t2)
        | NLam t11 <- t1' = beta t11
        | option == NF = mkNApp (normalizeWithSuspension t1' nilSuspension option) (normalizeWithSuspension t2 susp option)
        | option == HNF = mkNApp (normalizeWithSuspension t1' nilSuspension option) (mkSusp t2 susp)
        | option == WHNF = mkNApp t1' (mkSusp t2 susp)
        where
            t1' :: TermNode
            t1' = normalizeWithSuspension t1 susp WHNF
            beta :: TermNode -> TermNode
            beta (Susp t' (Suspension ol' nl' (Dummy l' : env')))
                | nl' == l' = normalizeWithSuspension t' (mkSuspension ol' (pred nl') (addBinds (mkSusp t2 susp) (pred l') env')) option
            beta t' = normalizeWithSuspension t' (mkSuspension 1 0 (addBinds (mkSusp t2 susp) 0 emptySuspensionEnv)) option
    dispatch (NLam t1)
        | option == WHNF = mkNLam (mkSusp t1 susp1)
        | otherwise = mkNLam (normalizeWithSuspension t1 susp1 option)
        where
            susp1 :: Suspension
            susp1 = mkSuspension (succ ol) (succ nl) (addDummy (succ nl) env)
    dispatch (NFun {})
        = t
    dispatch (Meta {})
        = t
    dispatch (Susp t' susp')
        | ol' == 0 && nl' == 0 = normalizeWithSuspension t' susp option
        | ol == 0 = normalizeWithSuspension t' (mkSuspension ol' (nl + nl') env') option
        | otherwise = normalizeWithSuspension (normalizeWithSuspension t' susp' WHNF) susp option
        where
            ol' :: Nat_ol
            ol' = _susp_ol susp'
            nl' :: Nat_nl
            nl' = _susp_nl susp'
            env' :: SuspensionEnv
            env' = _susp_env susp'

mkNIdx :: DeBruijnIndex -> TermNode
mkNIdx i = if i >= 0 then NIdx i else error "***mkNIdx: A negative De-Bruijn index given..."
{-# INLINABLE mkNIdx #-}

mkNCtr :: Identifier DataConstructorName -> TermNode
mkNCtr c = NCtr $! c
{-# INLINABLE mkNCtr #-}

mkNApp :: TermNode -> TermNode -> TermNode
mkNApp t1 t2 = (NApp $! t1) $! t2
{-# INLINABLE mkNApp #-}

mkNLam :: TermNode -> TermNode
mkNLam t1 = NLam $! t1
{-# INLINABLE mkNLam #-}

mkNFun :: Identifier ReferenceName -> TermNode
mkNFun f = NFun $! f
{-# INLINABLE mkNFun #-}

mkMeta :: Identifier MetaVariableName -> TermNode
mkMeta x = Meta $! x
{-# INLINABLE mkMeta #-}

mkSusp :: TermNode -> Suspension -> TermNode
mkSusp t susp
    | NCtr {} <- t = t
    | NFun {} <- t = t
    | Meta {} <- t = t
    | susp == nilSuspension = t
    | otherwise = Susp t susp
{-# INLINABLE mkSusp #-}

addDummy :: Nat -> SuspensionEnv -> SuspensionEnv
addDummy l env = l `seq` env `seq` Dummy l : env
{-# INLINABLE addDummy #-}

addBinds :: TermNode -> Nat -> SuspensionEnv -> SuspensionEnv
addBinds t l env = t `seq` l `seq` env `seq` Binds t l : env
{-# INLINABLE addBinds #-}

emptySuspensionEnv :: SuspensionEnv
emptySuspensionEnv = []
{-# INLINABLE emptySuspensionEnv #-}

nilSuspension :: Suspension
nilSuspension = Suspension 0 0 emptySuspensionEnv
{-# INLINABLE nilSuspension #-}

mkSuspension :: Nat_ol -> Nat_nl -> SuspensionEnv -> Suspension
mkSuspension ol nl env
    | ol /= length env = error "***mkSuspension: ol /= length env..."
    | nl < 0 = error "***mkSuspension: nl < 0..."
    | otherwise = Suspension ol nl env
{-# INLINABLE mkSuspension #-}

instance Show name => Outputable (Identifier name) where
    pprint _ (Identifier { nameOf = name }) = shows name
