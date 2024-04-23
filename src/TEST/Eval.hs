module TEST.Eval where

import Debug.Trace

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
    = ("<< fix " ++ show t1 ++ ", ol = " ++ show ol ++ ", nl = " ++ show nl ++ ", env = " ++ show env ++ " >>") `trace'`
        rewriteWithSusp t1 (succ ol) (succ nl) (Binds (mkSusp (FixTerm t1) ol nl env) (succ nl) : env) option
rewriteWithSusp (MatTerm t pats) ol nl env option
    = case unfoldApp (rewriteWithSusp t ol nl env NF) of
        (ConTerm cstr, ts) -> case cstr `lookup` pats of
            Nothing -> error ("no constructor match = " ++ show cstr)
            Just t1 -> ("{{ ts = " ++ show ts ++ ", t = " ++ show t1 ++ ", ol = " ++ show ol ++ ", nl = " ++ show nl ++ ", env = " ++ show env ++ " }}") `trace'`
                rewriteWithSusp t1 (length ts + ol) nl ([ Binds t nl | (i, t) <- zip [1 .. length ts] ts ] ++ env) option
        (t, ts) -> "??" `trace` foldl AppTerm t ts
{- rewriteWithSusp (MatTerm t pats) ol nl env option
    = case unfoldApp (rewriteWithSusp t ol nl env NF) of
        (ConTerm cstr, ts) -> case cstr `lookup` pats of
            Nothing -> error ("no constructor match = " ++ show cstr)
            Just t1 -> ("{{ t = " ++ show t1 ++ ", ol = " ++ show ol ++ ", nl = " ++ show nl ++ ", env = " ++ show env ++ " }}") `trace'`
                rewriteWithSusp t1 (length ts + ol) nl ([ Binds t nl | (i, t) <- zip [1 .. length ts] ts ] ++ env) option
        (t, ts) -> "??" `trace` foldl AppTerm t ts -}
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

test1 :: IO ()
test1 = print $! rewrite NF t where
    t :: Term
    t = AppTerm (AppTerm add two) zero
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
    add = fix_ (lam_ (lam_ (mat_ (idx_ 0) [(zer_, idx_ 1), (suc_, app_ (con_ suc_) (app_ (app_ (idx_ 2) (idx_ 0)) (idx_ 1)))]))) where
        fix_ = FixTerm
        lam_ = LamTerm
        mat_ = MatTerm
        con_ = ConTerm
        app_ = AppTerm
        idx_ = IdxTerm
        suc_ = "succ"
        zer_ = "zero"

trace' = const id
