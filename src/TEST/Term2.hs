module TEST.Term2 where

import Data.List
import Z.Utils

type DeBruijnIndex = Nat

type DataConstructorName = String

type IndividualVariableName = String

type Nat_ol = Nat

type Nat_nl = Nat

type SuspensionEnv = List SuspensionEnvItem

data Term
    = Var (IndividualVariableName)
    | Ctr (DataConstructorName)
    | App (Term) (Term)
    | Lam (IndividualVariableName) (Term)
    | Fix (IndividualVariableName) (Term)
    | Mat (Term) (List ((DataConstructorName, List IndividualVariableName), Term))
    deriving (Eq, Ord, Show)

data Identifier name
    = Identifier { getName :: name }
    deriving (Eq, Ord, Show)

data ReductionOption
    = WHNF
    | HNF
    | NF
    deriving (Eq, Ord, Show)

data TermNode
    = NIdx (DeBruijnIndex)
    | NCtr (Identifier DataConstructorName)
    | NApp (TermNode) (TermNode)
    | NLam (TermNode)
    | NFix (TermNode)
    | NMat (TermNode) (List (Identifier DataConstructorName, (Nat, TermNode)))
    | Susp (TermNode) (Suspension)
    deriving (Eq, Ord, Show)

data SuspensionEnvItem
    = Hole (Int)
    | Bind (TermNode) (Int)
    deriving (Eq, Ord, Show)

data Suspension
    = Suspension { _susp_ol :: Nat_ol, _susp_nl :: Nat_nl, _susp_env :: SuspensionEnv }
    deriving (Eq, Ord, Show)

convertTermToTermNode :: Term -> TermNode
convertTermToTermNode = go [] where
    go :: List IndividualVariableName -> Term -> TermNode
    go env (Var x) = maybe (error "***convertTermToTermNode: An open term given...") mkNIdx (x `elemIndex` env)
    go env (Ctr c) = mkNCtr (Identifier { getName = c })
    go env (App t1 t2) = mkNApp (go env t1) (go env t2)
    go env (Lam y t1) = mkNLam (go (y : env) t1)
    go env (Fix y t1) = mkNFix (go (y : env) t1)
    go env (Mat t1 bs) = mkNMat (go env t1) [ (Identifier { getName = c }, (length ys, go (ys ++ env) t)) | ((c, ys), t) <- bs ]

test1 :: IO ()
test1 = testnormalize testnormnalizecase1 where
    testnormalize :: TermNode -> IO ()
    testnormalize = putStrLn . pshow . normalize NF
    testnormnalizecase1 :: TermNode
    testnormnalizecase1 = mkNApp (mkNApp add three) five where
        zero :: TermNode
        zero = mkNCtr (Identifier "O")
        one :: TermNode
        one = mkNApp (mkNCtr (Identifier "S")) zero
        two :: TermNode
        two = mkNApp (mkNCtr (Identifier "S")) one
        three :: TermNode
        three = mkNApp (mkNCtr (Identifier "S")) two
        four :: TermNode
        four = mkNApp (mkNCtr (Identifier "S")) three
        five :: TermNode
        five = mkNApp (mkNCtr (Identifier "S")) four
        add :: TermNode -- = [| fix (\add -> \n -> \m -> case n of { O -> m; S n' -> S (add n' m) }) |]
        add = (fix_ (lam_ (lam_ (mat_ (idx_ 1) [(zer_, (0, idx_ 0)), (suc_, (1, app_ (con_ suc_) (app_ (app_ (idx_ 3) (idx_ 0)) (idx_ 1))))])))) where
            fix_ = mkNFix
            lam_ = mkNLam
            mat_ = mkNMat
            con_ = mkNCtr
            app_ = mkNApp
            idx_ = mkNIdx
            zer_ = Identifier "O"
            suc_ = Identifier "S"

test2 :: IO ()
test2 = go (mkSusp (mkNLam (mkNIdx 0)) (mkSuspension 1 1 (addHole 1 emptySuspensionEnv))) where
    go :: TermNode -> IO ()
    go = putStrLn . pshow . normalize WHNF

test3 :: IO ()
test3 = go (convertTermToTermNode term) where
    go :: TermNode -> IO ()
    go = putStrLn . pshow . normalize NF
    term :: Term -- case Mk One Two of { Mk x y -> Mk x y }
    term = Mat (App (App (Ctr "Mk") (Ctr "One")) (Ctr "Two")) [(("Mk", ["x", "y"]), App (App (Ctr "Mk") (Var "x")) (Var "y"))]

test4 :: IO ()
test4 = go (convertTermToTermNode term) where
    go :: TermNode -> IO ()
    go = putStrLn . pshow . normalize NF
    term :: Term -- (\f -> \a -> \b -> case f b of { Mk1 c d -> Mk1 c d; Mk2 e -> e }) (\x -> x)
    term = App (Lam "f" (Lam "a" (Lam "b" (Mat (App (Var "f") (Var "b")) [(("Mk1", ["c", "d"]), App (App (Ctr "Mk1") (Var "c")) (Var "d")), (("Mk2", ["e"]), Var "e")])))) (Lam "x" (Var "x"))

test5 :: IO ()
test5 = go (convertTermToTermNode term) where
    go :: TermNode -> IO ()
    go = putStrLn . pshow . normalize NF -- (\f -> f (Mk One Two)) (\a -> case a of { Mk b c -> Mk b c })
    term :: Term
    term = App (Lam "f" (App (Var "f") (App (App (Ctr "Mk") (Ctr "One")) (Ctr "Two")))) (Lam "a" (Mat (Var "a") [(("Mk", ["b", "c"]), App (App (Ctr "Mk") (Var "b")) (Var "c"))]))

test6 :: IO ()
test6 = testcase case6 where
    testcase :: TermNode -> IO ()
    testcase = putStrLn . pshow
    case6 :: TermNode
    case6 = mkNApp (mkNApp add three) five where
        zero :: TermNode
        zero = mkNCtr (Identifier "O")
        one :: TermNode
        one = mkNApp (mkNCtr (Identifier "S")) zero
        two :: TermNode
        two = mkNApp (mkNCtr (Identifier "S")) one
        three :: TermNode
        three = mkNApp (mkNCtr (Identifier "S")) two
        four :: TermNode
        four = mkNApp (mkNCtr (Identifier "S")) three
        five :: TermNode
        five = mkNApp (mkNCtr (Identifier "S")) four
        add :: TermNode -- = [| fix (\add -> \n -> \m -> case n of { O -> m; S n' -> S (add n' m) }) |]
        add = (fix_ (lam_ (lam_ (mat_ (idx_ 1) [(zer_, (0, idx_ 0)), (suc_, (1, app_ (con_ suc_) (app_ (app_ (idx_ 3) (idx_ 0)) (idx_ 1))))])))) where
            fix_ = mkNFix
            lam_ = mkNLam
            mat_ = mkNMat
            con_ = mkNCtr
            app_ = mkNApp
            idx_ = mkNIdx
            zer_ = Identifier "O"
            suc_ = Identifier "S"

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
    dispatch (NCtr {})
        = t
    dispatch (NApp t1 t2)
        | NLam t11 <- t1' = beta t11
        | option == WHNF = mkNApp t1' (mkSusp t2 susp)
        | option == HNF = mkNApp (normalize option t1') (mkSusp t2 susp)
        | option == NF = mkNApp (normalize option t1') (normalizeWithSuspension t2 susp option)
        where
            t1' :: TermNode
            t1' = normalizeWithSuspension t1 susp WHNF
            beta :: TermNode -> TermNode
            beta (Susp t' (Suspension ol' nl' (Hole l' : env')))
                | nl' == l' = normalizeWithSuspension t' (mkSuspension ol' (pred nl') (addBind (mkSusp t2 susp) (pred l') env')) option
            beta t' = normalizeWithSuspension t' (mkSuspension 1 0 (addBind (mkSusp t2 susp) 0 emptySuspensionEnv)) option
    dispatch (NLam t1)
        | option == WHNF = mkNLam (mkSusp t1 susp1)
        | otherwise = mkNLam (normalizeWithSuspension t1 susp1 option)
        where
            susp1 :: Suspension
            susp1 = mkSuspension (succ ol) (succ nl) (addHole (succ nl) env)
    dispatch (NFix t1)
        = normalizeWithSuspension t1 (mkSuspension (succ ol) nl (addBind (mkSusp t susp) nl env)) option
    dispatch (NMat t1 bs)
        | (NCtr c, ts) <- unfoldNApp t1' = iota ts (c `lookup` bs)
        | option == WHNF = mkNMat t1' [ (c, (n, mkSusp t (mkSuspension (ol + n) (nl + n) (foldr (\i -> addHole i) env [nl + n, nl + n - 1 .. nl + 1])))) | (c, (n, t)) <- bs ]
        | option == HNF = mkNMat (normalize option t1') [ (c, (n, mkSusp t (mkSuspension (ol + n) (nl + n) (foldr (\i -> addHole i) env [nl + n, nl + n - 1 .. nl + 1])))) | (c, (n, t)) <- bs ]
        | option == NF = mkNMat (normalize option t1') [ (c, (n, normalizeWithSuspension t (mkSuspension (ol + n) (nl + n) (foldr (\i -> addHole i) env [nl + n, nl + n - 1 .. nl + 1])) option)) | (c, (n, t)) <- bs ]
        where
            t1' :: TermNode
            t1' = normalizeWithSuspension t1 susp WHNF
            iota :: List TermNode -> Maybe (Nat, TermNode) -> TermNode
            iota ts (Just (n, t'))
                | length ts == n = normalizeWithSuspension t' (mkSuspension (length ts + ol) nl (foldr (\t -> addBind t nl) env ts)) option
            iota ts _ = error "***normalizeWithSuspension: No matching constructor..."
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

mkNFix :: TermNode -> TermNode
mkNFix t1 = NFix $! t1
{-# INLINABLE mkNFix #-}

mkNMat :: TermNode -> List (Identifier DataConstructorName, (Nat, TermNode)) -> TermNode
mkNMat t1 bs = (NMat $! t1) $! bs
{-# INLINABLE mkNMat #-}

mkSusp :: TermNode -> Suspension -> TermNode
mkSusp t susp
    | NCtr {} <- t = t
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

instance (Show name) => Outputable (Identifier name) where
    pprint _ (Identifier { getName = name }) = shows name

instance Outputable TermNode where
    pprint prec
        | prec == 0 = go [] 0
        | otherwise = \t -> strstr "(" . go [] 0 t . strstr ")"
        where
            go :: [Int] -> Prec -> TermNode -> ShowS
            go name 0 (NLam t1) = strstr "fun " . strstr "W_" . shows (length name) . strstr " => " . go (length name : name) 0 t1
            go name 0 (NFix t1) = strstr "fix " . strstr "W_" . shows (length name) . strstr " := " . go (length name : name) 0 t1
            go name 0 t = go name 1 t
            go name 1 (NApp t1 t2) = go name 1 t1 . strstr " " . go name 2 t2
            go name 1 t = go name 2 t
            go name 2 (NIdx i) = strstr "W_" . shows (name !! i)
            go name 2 (NCtr c) = strstr (getName c)
            go name 2 (Susp t susp) = strstr "(" . pprint 3 t . strstr " with { ol = " . shows (_susp_ol susp) . strstr ", nl = " . shows (_susp_nl susp) . strstr ", env = " . strcat [ item name it | it <- _susp_env susp ] . strstr "})"
            go name 2 t = go name 3 t
            go name 3 (NMat t1 bs) = strstr "match " . go name 0 t1 . strstr " with\n" . strcat [ strstr "| " . strstr (getName c) . strcat [ strstr " " . strstr "W_" . shows i | i <- [length name .. length name + n - 1] ] . strstr " => " . go ([length name .. length name + n - 1] ++ name) 0 t . strstr "\n" | (c, (n, t)) <- bs ] . strstr "end"
            go name _ t = strstr "(" . go name 0 t . strstr ")"
            item :: [Int] -> SuspensionEnvItem -> ShowS
            item name (Hole l) = strstr "@" . shows l . strstr " "
            item name (Bind t l) = strstr "(" . go name 0 t . strstr ", " . shows l . strstr ") "

instance Outputable Term where
    pprint 0 (Lam y t1) = strstr "lam " . strstr y . strstr ". " . pprint 0 t1
    pprint 0 (Fix y t1) = strstr "fix " . strstr y . strstr ". " . pprint 0 t1
    pprint 0 t = pprint 1 t
    pprint 1 (App t1 t2) = pprint 1 t1 . strstr " " . pprint 2 t2
    pprint 1 t = pprint 2 t
    pprint 2 (Var x) = strstr x
    pprint 2 (Ctr c) = strstr c
    pprint 2 (Mat t1 bs) = strstr "match " . pprint 0 t1 . strstr " with" . strcat [ strstr " | " . strstr c . strcat [ strstr " " . strstr y | y <- ys ] . strstr " => " . pprint 0 t | ((c, ys), t) <- bs ] . strstr " end"
    pprint _ t = strstr "(" . pprint 0 t . strstr ")"
