module HOL.Back.TermNode where

import HOL.Front.Ast
import Z.Utils

type DeBruijnIndex = Nat

type Nat_ol = Nat

type Nat_nl = Nat

type SuspensionEnv = List SuspensionEnvItem

data TermNode
    = NIdx !(DeBruijnIndex)
    | NCon (Name)
    | NApp !(TermNode) !(TermNode)
    | NLam (LargeId) !(TermNode)
    | Susp !(TermNode) (Suspension)
    deriving (Eq, Ord, Show)

data ReductionOption
    = WHNF
    | HNF
    | NF
    deriving (Eq, Ord, Show)

data SuspensionEnvItem
    = Hole !(Int)
    | Bind !(TermNode) !(Int)
    deriving (Eq, Ord, Show)

data Suspension
    = Suspension { _susp_ol :: Nat_ol, _susp_nl :: Nat_nl, _susp_env :: SuspensionEnv }
    deriving (Eq, Ord, Show)

normalize :: ReductionOption -> TermNode -> TermNode
normalize option t = normalizeWithSuspension t initialSuspension option
{-# INLINABLE normalize #-}

unfoldNApp :: TermNode -> (TermNode, List TermNode)
unfoldNApp = flip go [] where
    go :: TermNode -> List TermNode -> (TermNode, List TermNode)
    go (NApp t1 t2) ts = go t1 (t2 : ts)
    go t ts = (t, ts)

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
            Hole l -> mkNIdx (nl - l)
            Bind t' l -> normalizeWithSuspension t' (mkSuspension 0 (nl - l) []) option
        | otherwise = error "***normalizeWithSuspension: A negative De-Bruijn index given..."
    dispatch (NCon {})
        = t
    dispatch (NApp t1 t2)
        | NLam _ t11 <- t1' = beta t11
        | option == WHNF = mkNApp t1' (mkSusp t2 susp)
        | option == HNF = mkNApp (normalizeWithSuspension t1' initialSuspension option) (mkSusp t2 susp)
        | option == NF = mkNApp (normalizeWithSuspension t1' initialSuspension option) (normalizeWithSuspension t2 susp option)
        where
            t1' :: TermNode
            t1' = normalizeWithSuspension t1 susp WHNF
            beta :: TermNode -> TermNode
            beta (Susp t' (Suspension ol' nl' (Hole l' : env')))
                | nl' == l' = normalizeWithSuspension t' (mkSuspension ol' (pred nl') (addBind (mkSusp t2 susp) (pred l') env')) option
            beta t' = normalizeWithSuspension t' (mkSuspension 1 0 (addBind (mkSusp t2 susp) 0 emptySuspensionEnv)) option
    dispatch (NLam nm t1)
        | option == WHNF = mkNLam nm (mkSusp t1 susp1)
        | otherwise = mkNLam nm (normalizeWithSuspension t1 susp1 option)
        where
            susp1 :: Suspension
            susp1 = mkSuspension (succ ol) (succ nl) (addHole (succ nl) env)
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

mkNCon :: Name -> TermNode
mkNCon c = NCon $! c
{-# INLINABLE mkNCon #-}

mkNApp :: TermNode -> TermNode -> TermNode
mkNApp t1 t2 = (NApp $! t1) $! t2
{-# INLINABLE mkNApp #-}

mkNLam :: LargeId -> TermNode -> TermNode
mkNLam nm t1 = NLam nm $! t1
{-# INLINABLE mkNLam #-}

mkSusp :: TermNode -> Suspension -> TermNode
mkSusp t susp
    | NCon {} <- t = t
    | susp == initialSuspension = t
    | otherwise = Susp t susp
{-# INLINABLE mkSusp #-}

addHole :: Nat -> SuspensionEnv -> SuspensionEnv
addHole l env = l `seq` env `seq` Hole l : env
{-# INLINABLE addHole #-}

addBind :: TermNode -> Nat -> SuspensionEnv -> SuspensionEnv
addBind t l env = t `seq` l `seq` env `seq` Bind t l : env
{-# INLINABLE addBind #-}

emptySuspensionEnv :: SuspensionEnv
emptySuspensionEnv = []
{-# INLINE emptySuspensionEnv #-}

initialSuspension :: Suspension
initialSuspension = Suspension { _susp_ol = length emptySuspensionEnv, _susp_nl = 0, _susp_env = emptySuspensionEnv }
{-# INLINE initialSuspension #-}

mkSuspension :: Nat_ol -> Nat_nl -> SuspensionEnv -> Suspension
mkSuspension ol nl env
    | ol /= length env = error "***mkSuspension: ol /= length env..."
    | nl < 0 = error "***mkSuspension: nl < 0..."
    | otherwise = Suspension { _susp_ol = ol, _susp_nl = nl, _susp_env = env }
{-# INLINABLE mkSuspension #-}
