module TEST.Eval where

import Debug.Trace
import Z.Utils

type Constant = String

type DeBruijnIndex = Int

type Nat_ol = Int

type Nat_nl = Int

type SuspEnv = [SuspItem]

data Term
    = ConTerm Constant
    | IdxTerm DeBruijnIndex
    | AppTerm Term Term
    | LamTerm Term
    | FixTerm Term
    | MatTerm Term [(Constant, Term)]
    | Susp { body :: Term, ol :: Nat_ol, nl :: Nat_nl, env :: SuspEnv}
    deriving (Eq, Show)

data SuspItem
    = Dummy Int
    | Binds Term Int
    deriving (Eq, Show)

data ReduceOption
    = WHNF
    | HNF
    | NF
    deriving (Eq, Show)

mkSusp :: Term -> Nat_ol -> Nat_nl -> SuspEnv -> Term
mkSusp (ConTerm c) _ _ _ = ConTerm c
mkSusp t 0 0 [] = t
mkSusp t ol nl e = Susp t ol nl e

unfoldApp :: Term -> (Term, [Term])
unfoldApp (AppTerm t1 t2) = let (h, ts) = unfoldApp t1 in (h, ts ++ [t2])
unfoldApp t = (t, [])

rewriteWithSusp :: Term -> Nat_ol -> Nat_nl -> SuspEnv -> ReduceOption -> Term
rewriteWithSusp (IdxTerm i) ol nl env option
    | i >= ol = IdxTerm (i - ol + nl)
    | i >= 0 = case env !! i of
        Dummy l -> IdxTerm (nl - l)
        Binds t l -> rewriteWithSusp t 0 (nl - l) [] option
    | otherwise = error "A negative de-bruijn index."
rewriteWithSusp (AppTerm t1 t2) ol nl env option
    = case rewriteWithSusp t1 ol nl env WHNF of
        LamTerm t -> case t of
            Susp t' ol' nl' (Dummy l' : env')
                | nl' == l' -> rewriteWithSusp t' ol' (pred nl') (Binds (mkSusp t2 ol nl env) (pred l') : env') option
            t -> rewriteWithSusp t 1 0 [Binds (mkSusp t2 ol nl env) 0] option
        t1' -> case option of
            NF -> AppTerm (rewriteWithSusp t1' 0 0 [] option) (rewriteWithSusp t2 ol nl env option)
            HNF -> AppTerm (rewriteWithSusp t1' 0 0 [] option) (mkSusp t2 ol nl env)
            WHNF -> AppTerm t1' (mkSusp t2 ol nl env)
rewriteWithSusp (LamTerm t1) ol nl env option
    | option == WHNF = LamTerm (mkSusp t1 (succ ol) (succ nl) (Dummy (succ nl) : env))
    | otherwise = LamTerm (rewriteWithSusp t1 (succ ol) (succ nl) (Dummy (succ nl) : env) option)
rewriteWithSusp (FixTerm t1) ol nl env option
    = rewriteWithSusp t1 (succ ol) nl (Binds (mkSusp (FixTerm t1) ol nl env) nl : env) option
rewriteWithSusp (MatTerm t pats) ol nl env option
    = case unfoldApp (rewriteWithSusp t ol nl env WHNF) of
        (ConTerm cstr, ts) -> case cstr `lookup` pats of
            Nothing -> error "no matching constructor"
            Just t1 -> rewriteWithSusp t1 (length ts + ol) nl ([ Binds t nl | t <- ts ] ++ env) option
        (t, ts) -> foldl AppTerm t ts
rewriteWithSusp (Susp t ol nl env) ol' nl' env' option
    | ol == 0 && nl == 0 = rewriteWithSusp t ol' nl' env' option
    | ol' == 0 = rewriteWithSusp t ol (nl + nl') env option
    | otherwise = case rewriteWithSusp t ol nl env WHNF of
        LamTerm t1
            | option == WHNF -> LamTerm (mkSusp t1 (succ ol') (succ nl') (Dummy (succ nl') : env'))
            | otherwise -> LamTerm (rewriteWithSusp t1 (succ ol') (succ nl') (Dummy (succ nl') : env') option)
        t' -> rewriteWithSusp t' ol' nl' env' option
rewriteWithSusp t ol nl env option
    = mkSusp t ol nl env

rewrite :: ReduceOption -> Term -> Term
rewrite option t = rewriteWithSusp t 0 0 [] option

test1 :: Int -> IO ()
test1 cnt = putStrLn $! ppTerm (rewriteDBG cnt) where
    t :: Term
    t = AppTerm (AppTerm add three) three
    zero :: Term
    zero = ConTerm "zero"
    one :: Term
    one = AppTerm (ConTerm "succ") zero
    two :: Term
    two = AppTerm (ConTerm "succ") one
    three :: Term
    three = AppTerm (ConTerm "succ") two
    four :: Term
    four = AppTerm (ConTerm "succ") three
    five :: Term
    five = AppTerm (ConTerm "succ") four
    add :: Term -- fix add (n : nat) (m: nat) {struct n} : nat := match n with O => m | S n' => S (add n' m) end
    add = fix_ (lam_ (lam_ (mat_ (idx_ 1) [(zer_, idx_ 0), (suc_, app_ (con_ suc_) (app_ (app_ (idx_ 3) (idx_ 0)) (idx_ 1)))]))) where
        fix_ = FixTerm
        lam_ = LamTerm
        mat_ = MatTerm
        con_ = ConTerm
        app_ = AppTerm
        idx_ = IdxTerm
        suc_ = "succ"
        zer_ = "zero"
    rewriteDBG :: Int -> Term
    rewriteDBG = runDBG t 0 0 [] NF
    runDBG :: Term -> Nat_ol -> Nat_nl -> SuspEnv -> ReduceOption -> Int -> Term
    runDBG t ol nl env _ 0 = mkSusp t ol nl env
    runDBG (IdxTerm i) ol nl env option n
        | i >= ol = IdxTerm (i - ol + nl)
        | i >= 0 = case env !! i of
            Dummy l -> IdxTerm (nl - l)
            Binds t l -> runDBG t 0 (nl - l) [] option (pred n)
        | otherwise = error "A negative de-bruijn index."
    runDBG (AppTerm t1 t2) ol nl env option n
        = case runDBG t1 ol nl env WHNF (pred n) of
            LamTerm t -> case t of
                Susp t' ol' nl' (Dummy l' : env')
                    | nl' == l' -> runDBG t' ol' (pred nl') (Binds (mkSusp t2 ol nl env) (pred l') : env') option (pred n)
                t -> runDBG t 1 0 [Binds (mkSusp t2 ol nl env) 0] option (pred n)
            t1' -> case option of
                NF -> AppTerm (runDBG t1' 0 0 [] option (pred n)) (runDBG t2 ol nl env option (pred n))
                HNF -> AppTerm (runDBG t1' 0 0 [] option (pred n)) (mkSusp t2 ol nl env)
                WHNF -> AppTerm t1' (mkSusp t2 ol nl env)
    runDBG (LamTerm t1) ol nl env option n
        | option == WHNF = LamTerm (mkSusp t1 (succ ol) (succ nl) (Dummy (succ nl) : env))
        | otherwise = LamTerm (runDBG t1 (succ ol) (succ nl) (Dummy (succ nl) : env) option (pred n))
    runDBG (FixTerm t1) ol nl env option n
        = ("<< fix " ++ show t1 ++ ", ol = " ++ show ol ++ ", nl = " ++ show nl ++ ", env = " ++ show env ++ " >>") `trace'`
            runDBG t1 (succ ol) nl (Binds (mkSusp (FixTerm t1) ol nl env) nl : env) option (pred n)
        -- if the above is wrong, how about: runDBG t1 (succ ol) (succ nl) (Binds (mkSusp (FixTerm t1) ol (succ nl) env) nl : env) option (pred n)
    runDBG (MatTerm t pats) ol nl env option n
        = case unfoldApp (runDBG t ol nl env NF (pred n)) of
            (ConTerm cstr, ts) -> case cstr `lookup` pats of
                Nothing -> error "cannot find constructor"
                Just t1 -> runDBG t1 (length ts + ol) nl ([ Binds t nl | t <- ts ] ++ env) option (pred n)
            (t, ts) -> foldl AppTerm t ts
    {- rewriteWithSusp (MatTerm t pats) ol nl env option
        = case unfoldApp (rewriteWithSusp t ol nl env NF) of
            (ConTerm cstr, ts) -> case cstr `lookup` pats of
                Nothing -> error ("no constructor match = " ++ show cstr)
                Just t1 -> ("{{ t = " ++ show t1 ++ ", ol = " ++ show ol ++ ", nl = " ++ show nl ++ ", env = " ++ show env ++ " }}") `trace'`
                    rewriteWithSusp t1 (length ts + ol) nl ([ Binds t nl | (i, t) <- zip [1 .. length ts] ts ] ++ env) option
            (t, ts) -> "??" `trace` foldl AppTerm t ts -}
    runDBG (Susp t ol nl env) ol' nl' env' option n
        | ol == 0 && nl == 0 = runDBG t ol' nl' env' option (pred n)
        | ol' == 0 = runDBG t ol (nl + nl') env option (pred n)
        | otherwise = case runDBG t ol nl env WHNF n of
            LamTerm t1
                | option == WHNF -> LamTerm (mkSusp t1 (succ ol') (succ nl') (Dummy (succ nl') : env'))
                | otherwise -> LamTerm (runDBG t1 (succ ol') (succ nl') (Dummy (succ nl') : env') option (pred n))
            t' -> runDBG t' ol' nl' env' option (pred n)
    runDBG t ol nl env option n
        = mkSusp t ol nl env

trace' = const id

ppTerm :: Term -> String
ppTerm = flip (go 0) ""  where
    unNum :: Term -> Maybe Int
    unNum (ConTerm "zero") = pure 0
    unNum (AppTerm (ConTerm "succ") t1) = succ <$> unNum t1
    unNum _ = Nothing
    go :: Int -> Term -> String -> String
    go 0 (LamTerm t1) = strstr "lam " . go 0 t1  
    go 0 (FixTerm t1) = strstr "fix " . go 0 t1
    go 0 t = maybe (go 1 t) shows (unNum t)
    go 1 (AppTerm t1 t2) = go 1 t1 . strstr " " . go 2 t2
    go 1 t = go 2 t
    go 2 (IdxTerm i) = strstr "#" . shows i
    go 2 (ConTerm c) = strstr c
    go 2 (MatTerm t1 ks) = strstr "(match " . go 0 t1 . strstr " with\n" . strcat [ strstr "| " . strstr c . strstr " => " . go 0 t . strstr "\n" | (c, t) <- ks ] . strstr "end)"
    go 2 (Susp t ol nl env) = strstr "[body = " . go 3 t . strstr " with { ol = " . shows ol . strstr ", nl = " . shows nl . strstr ", env = " . strcat [ ppSuspItem it | it <- env ] . strstr "}]"
    go _ t = maybe (strstr "(" . go 0 t . strstr ")") shows (unNum t)
    ppSuspItem :: SuspItem -> String -> String
    ppSuspItem (Dummy l) = strstr "@" . shows l . strstr ", "
    ppSuspItem (Binds t l) = strstr "(" . go 0 t . strstr ", @" . shows l . strstr "), "

{-  = ConTerm Constant
    | IdxTerm DeBruijnIndex
    | AppTerm Term Term
    | LamTerm Term
    | FixTerm Term
    | MatTerm Term [(Constant, Term)]
    | Susp { body :: Term, ol :: Nat_ol, nl :: Nat_nl, env :: SuspEnv}
-}
