{-# LANGUAGE DeriveFunctor #-}
module ALPHA1.TermNode where

import ALPHA1.Ast
import Z.Utils

type DeBruijnIndex = Nat

type Nat_ol = Nat

type Nat_nl = Nat

type SuspensionEnv = List SuspensionEnvItem

data TermNode
    = LVar (LVar)
    | NIdx !(DeBruijnIndex)
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
    dispatch (LVar {})
        = t
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

mkLVar :: LVar -> TermNode
mkLVar x = LVar $! x

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

viewNestedNLam :: TermNode -> (Int, TermNode)
viewNestedNLam = go 0 where
    go :: Int -> TermNode -> (Int, TermNode)
    go n (NLam x t) = go (n + 1) t
    go n t = (n, t)

makeNestedNLam :: Int -> TermNode -> TermNode
makeNestedNLam n
    | n == 0 = id
    | n > 0 = makeNestedNLam (n - 1) . mkNLam "W"
    | otherwise = undefined

etaReduce :: TermNode -> TermNode
etaReduce = go . normalize NF where
    isFreeIn :: DeBruijnIndex -> TermNode -> Bool
    isFreeIn i (NIdx j) = i == j
    isFreeIn i (NApp t1 t2) = isFreeIn i t1 || isFreeIn i t2
    isFreeIn i (NLam _ t1) = isFreeIn (i + 1) t1
    isFreeIn i _ = False
    decr :: TermNode -> TermNode
    decr (LVar x) = mkLVar x
    decr (NIdx i) = if i > 0 then mkNIdx (i - 1) else error "etaReduce.decr: unreachable..."
    decr (NCon c) = mkNCon c
    decr (NApp t1 t2) = mkNApp (decr t1) (decr t2)
    decr (NLam x t1) = mkNLam x (decr t1)
    go :: TermNode -> TermNode
    go (LVar x) = mkLVar x
    go (NIdx i) = mkNIdx i
    go (NCon c) = mkNCon c
    go (NApp t1 t2) = mkNApp (go t1) (go t2)
    go (NLam x t1) = case go t1 of
        NApp t1' (NIdx 0)
            | not (isFreeIn 0 t1') -> decr t1'
        t1' -> mkNLam x t1'

instance Outputable TermNode where
    pprint prec = (mkNameEnv >>= go prec 0) . normalize NF where
        myPrecIs :: Prec -> Prec -> ShowS -> ShowS
        myPrecIs prec prec' ss = if prec > prec' then strstr "(" . ss . strstr ")" else ss
        showLVar :: LVar -> ShowS
        showLVar (LVarNamed x) = strstr x
        showLVar (LVarUnique u) = strstr "?V_" . shows (unUnique u)
        showName :: Name -> ShowS
        showName (QualifiedName _ nm) = strstr nm
        showName (UniquelyGened u _) = strstr "#c_" . shows (unUnique u)
        mkName :: String -> [String] -> String
        mkName x env = gen 1 where
            gen :: Int -> String
            gen seed = let nm = x ++ "_" ++ show seed in if nm `elem` env then gen (seed + 1) else nm
        mkNameEnv :: TermNode -> [String]
        mkNameEnv (LVar x) = [showLVar x ""]
        mkNameEnv (NIdx i) = []
        mkNameEnv (NCon c) = [showName c ""]
        mkNameEnv (NApp t1 t2) = mkNameEnv t1 ++ mkNameEnv t2
        mkNameEnv (NLam x t1) = mkNameEnv t1 
        go :: Prec -> Int -> [String] -> TermNode -> ShowS
        go prec j env (LVar x) = showLVar x
        go prec j env (NIdx i) = if i < j then strstr (env !! i) else error "pprint: not a closed term"
        go prec j env (NCon c) = showName c
        go prec j env (NApp t1 t2) = myPrecIs prec 9 $ go 9 j env t1 . strstr " " . go 10 j env t2
        go prec j env (NLam x t1) = let nm = mkName x env in myPrecIs prec 0 $ strstr nm . strstr "\\ " . go 0 (j + 1) (nm : env) t1
