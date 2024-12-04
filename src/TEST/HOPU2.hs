module TEST.HOPU2 (hopu2) where

import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.State.Strict
import Control.Monad.Trans.Writer
import Data.Char
import Data.Foldable
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import ALPHA1.TermNode
import ALPHA1.Ast
import Z.Algorithms
import Z.Utils

infix 4 +->

infix 6 :=?=:

type Constant = Name

type LogicVar = LVar

type ScopeLevel = Int

type LVarSubst = VarBinding

type HasChanged = Bool

data Labeling
    = Labeling
        { _ConLabel :: Map.Map Constant ScopeLevel
        , _VarLabel :: Map.Map LogicVar ScopeLevel
        }
    deriving (Eq, Ord, Show)

data Disagreement
    = TermNode :=?=: TermNode
    deriving (Eq, Ord, Show)

data HopuSol
    = HopuSol
        { _ChangedLabelingEnv :: Labeling
        , _MostGeneralUnifier :: LVarSubst
        }
    deriving (Eq, Ord, Show)

data HopuFail
    = DownFail
    | UpFail
    | OccursCheckFail
    | FlexRigidFail
    | RigidRigidFail
    | BindFail
    | NotAPattern
    deriving (Eq, Ord, Show)

newtype VarBinding
    = VarBinding { unVarBinding :: Map.Map LogicVar TermNode }
    deriving (Eq, Ord, Show)

class Labelable atom where
    enrollLabel :: atom -> ScopeLevel -> Labeling -> Labeling
    updateLabel :: atom -> ScopeLevel -> Labeling -> Labeling
    lookupLabel :: atom -> Labeling -> ScopeLevel

class HasLVar expr where
    accLVars :: expr -> Set.Set LogicVar -> Set.Set LogicVar
    bindVars :: VarBinding -> expr -> expr

class ZonkLVar expr where
    zonkLVar :: LVarSubst -> expr -> expr

hopu2 :: IO ()
hopu2 = go (Labeling { _ConLabel = Map.empty, _VarLabel = Map.empty }) [] where
    example1 :: [String]
    example1 =
        [ "add con \"f\" 0"
        , "add con \"c\" 1"
        , "add con \"d\" 2"
        , "add var \"X\" 0"
        , "add var \"Y\" 0"
        , "add var \"Z\" 0"
        , "add eqn \"X c ~ f (Y c d) (Z c c)\""
        , "solve"
        ]
    {- example2
add con "f" 0
add con "c" 1
add con "d" 2
add var "X" 0
add var "Y" 0
add var "Z" 0
add eqn "(W\\ X c W) ~ (W\\ f (Y c d) (Z c d c W) W)"
solve
    -}
    go :: Labeling -> [Disagreement] -> IO ()
    go labeling disagrees = do
        s <- getLine
        case swords s of
            [] -> putStrLn "quit"
            ["add", "var", var, level] -> go (enrollLabel (LVarNamed $! var) (read level) labeling) disagrees
            ["add", "con", con, level] -> go (enrollLabel (QualifiedName NoQual $! con) (read level) labeling) disagrees
            ["add", "eqn", eqn] -> do
                eqn <- return $! readDisagreement eqn
                go labeling (eqn : disagrees)
            ["solve"] -> do
                res <- execUniqueT (runHOPU labeling disagrees)
                case res of
                    Nothing -> putStrLn "no solution..."
                    Just (disagrees', HopuSol labeling' mgu) -> do
                        putStrLn ("leftDisagreements = " ++ plist 4 (map (pprint 0) disagrees') "")
                        putStrLn ("finalLabeling = " ++ pprint 0 labeling' "")
                        putStrLn ("theMostGeneralUnifier = " ++ pprint 0 mgu "")
            _ -> go labeling disagrees

isRigidAtom :: TermNode -> Bool
isRigidAtom (NCon {}) = True
isRigidAtom (NIdx {}) = True
isRigidAtom _ = False

isPatternRespectTo :: LogicVar -> [TermNode] -> Labeling -> Bool
isPatternRespectTo v ts labeling = all isRigidAtom ts && areAllDistinct ts && and [ lookupLabel v labeling < lookupLabel c labeling | NCon c <- ts ]

down :: Monad m => [TermNode] -> [TermNode] -> StateT Labeling (ExceptT HopuFail m) [TermNode]
zs `down` ts = if downable then return indices else lift (throwE DownFail) where
    downable :: Bool
    downable = areAllDistinct ts && all isRigidAtom ts && areAllDistinct zs && all isRigidAtom zs
    indices :: [TermNode]
    indices = [ mkNIdx (length ts - i - 1) | z <- zs, i <- toList (z `List.elemIndex` ts) ]

up :: Monad m => [TermNode] -> LogicVar -> StateT Labeling (ExceptT HopuFail m) [TermNode]
ts `up` y = if upable then fmap findVisibles get else lift (throwE UpFail) where
    upable :: Bool
    upable = areAllDistinct ts && all isRigidAtom ts
    findVisibles :: Labeling -> [TermNode]
    findVisibles labeling = [ mkNCon c | NCon c <- ts, lookupLabel c labeling <= lookupLabel y labeling ]

bind :: LogicVar -> TermNode -> [TermNode] -> Int -> StateT Labeling (ExceptT HopuFail (UniqueT IO)) (LVarSubst, TermNode)
bind var = go . normalize HNF where
    go :: TermNode -> [TermNode] -> Int -> StateT Labeling (ExceptT HopuFail (UniqueT IO)) (LVarSubst, TermNode)
    go rhs parameters lambda
        | (lambda', rhs') <- viewNestedNLam rhs
        , lambda' > 0
        = do
            (subst, lhs') <- go rhs' parameters (lambda + lambda')
            return (subst, makeNestedNLam lambda' lhs')
        | (rhs_head, rhs_tail) <- unfoldNApp rhs
        , isRigidAtom rhs_head
        = do
            labeling <- get
            let foldbind [] = return (mempty, [])
                foldbind (rhs_tail_elements : rhs_tail) = do
                    (subst, lhs_tail_elements) <- go (normalize HNF rhs_tail_elements) parameters lambda
                    (theta, lhs_tail) <- foldbind (bindVars subst rhs_tail)
                    return (theta <> subst, bindVars theta lhs_tail_elements : lhs_tail)
                getLhsHead lhs_arguments
                    | NCon con <- rhs_head
                    , lookupLabel var labeling >= lookupLabel con labeling
                    = return rhs_head
                    | Just idx <- rhs_head `List.elemIndex` lhs_arguments
                    = return (mkNIdx (length lhs_arguments - idx - 1))
                    | otherwise
                    = lift (throwE FlexRigidFail)
            lhs_head <- getLhsHead ([ normalizeWithSuspension param (mkSuspension 0 lambda []) NF | param <- parameters ] ++ map mkNIdx [lambda - 1, lambda - 2 .. 0])
            (subst, lhs_tail) <- foldbind rhs_tail
            return (subst, List.foldl' mkNApp lhs_head lhs_tail)
        | (LVar var', rhs_tail) <- unfoldNApp rhs
        = do
            when (var == var') $ lift (throwE OccursCheckFail)
            labeling <- get
            let lhs_arguments = [ normalizeWithSuspension param (mkSuspension 0 lambda []) NF | param <- parameters ] ++ map mkNIdx [lambda - 1, lambda - 2 .. 0]
                rhs_arguments = map (normalize NF) rhs_tail
                common_arguments = Set.toList (Set.fromList lhs_arguments `Set.intersection` Set.fromList rhs_arguments)
                cmp_res = lookupLabel var labeling `compare` lookupLabel var' labeling
            if isPatternRespectTo var' rhs_arguments labeling then do
                (lhs_inner, rhs_inner) <- case cmp_res of
                    LT -> do
                        selected_rhs_parameters <- lhs_arguments `up` var'
                        selected_lhs_parameters <- selected_rhs_parameters `down` lhs_arguments
                        return (selected_lhs_parameters, selected_rhs_parameters)
                    _ -> do
                        selected_lhs_parameters <- rhs_arguments `up` var
                        selected_rhs_parameters <- selected_lhs_parameters `down` rhs_arguments
                        return (selected_lhs_parameters, selected_rhs_parameters)
                lhs_outer <- common_arguments `down` lhs_arguments
                rhs_outer <- common_arguments `down` rhs_arguments
                common_head <- getNewLVar (lookupLabel var labeling)
                theta <- lift $ var' +-> makeNestedNLam (length rhs_tail) (List.foldl' mkNApp common_head (rhs_inner ++ rhs_outer))
                modify (zonkLVar theta)
                return (theta, List.foldl' mkNApp common_head (lhs_inner ++ lhs_outer))
            else if cmp_res /= LT && all isRigidAtom rhs_arguments && and [ lookupLabel c labeling > lookupLabel var labeling | NCon c <- rhs_arguments ] then do
                common_head <- getNewLVar (lookupLabel var' labeling)
                theta <- lift $ var' +-> makeNestedNLam (length rhs_arguments) (List.foldl' mkNApp common_head [ mkNIdx (length rhs_arguments - i - 1) | i <- [0, 1 .. length rhs_arguments - 1], rhs_arguments !! i `elem` common_arguments ])
                modify (zonkLVar theta)
                return (theta, List.foldl' mkNApp common_head [ mkNIdx (length lhs_arguments - i - 1) | z <- rhs_arguments, i <- toList (z `List.elemIndex` lhs_arguments) ])
            else lift (throwE NotAPattern)
        | otherwise
        = lift (throwE BindFail)

mksubst :: LogicVar -> TermNode -> [TermNode] -> Labeling -> ExceptT HopuFail (UniqueT IO) (Maybe HopuSol)
mksubst var rhs parameters labeling = catchE (Just . uncurry (flip HopuSol) <$> runStateT (go var (normalize HNF rhs) parameters) labeling) handleErr where
    go :: LogicVar -> TermNode -> [TermNode] -> StateT Labeling (ExceptT HopuFail (UniqueT IO)) LVarSubst
    go var rhs parameters
        | (lambda, rhs') <- viewNestedNLam rhs
        , (LVar var', rhs_tail) <- unfoldNApp rhs'
        , var == var'
        = do
            labeling <- get
            let n = length parameters + lambda
                lhs_arguments = [ normalizeWithSuspension param (mkSuspension 0 lambda []) NF | param <- parameters ] ++ map mkNIdx [lambda - 1, lambda - 2 .. 0]
                rhs_arguments = map (normalize NF) rhs_tail
                common_arguments = [ mkNIdx (n - i - 1) | i <- [0, 1 .. n - 1], lhs_arguments !! i == rhs_arguments !! i ]
            if lhs_arguments == rhs_arguments then
                return mempty
            else do
                unless (isPatternRespectTo var' rhs_arguments labeling) $ lift (throwE NotAPattern)
                common_head <- getNewLVar (lookupLabel var labeling)
                theta <- lift $ var' +-> makeNestedNLam n (List.foldl' mkNApp common_head common_arguments)
                modify (zonkLVar theta)
                return theta
        | otherwise
        = do
            labeling <- get
            let n = length parameters
                lhs_arguments = map (normalize NF) parameters
            unless (isPatternRespectTo var lhs_arguments labeling) $ lift (throwE NotAPattern)
            (subst, lhs) <- bind var rhs parameters 0
            theta <- lift $ var +-> makeNestedNLam n lhs
            modify (zonkLVar theta)
            return (theta <> subst)
    handleErr :: HopuFail -> ExceptT HopuFail (UniqueT IO) (Maybe HopuSol)
    handleErr NotAPattern = return Nothing
    handleErr err = throwE err

simplify :: [Disagreement] -> Labeling -> StateT HasChanged (ExceptT HopuFail (UniqueT IO)) ([Disagreement], HopuSol)
simplify = flip loop mempty . zip (repeat 0) where
    loop :: [(Int, Disagreement)] -> LVarSubst -> Labeling -> StateT HasChanged (ExceptT HopuFail (UniqueT IO)) ([Disagreement], HopuSol)
    loop [] subst labeling = return ([], HopuSol labeling subst)
    loop ((l, lhs :=?=: rhs) : disagreements) subst labeling = dispatch l (normalize NF lhs) (normalize NF rhs) where
        dispatch :: Int -> TermNode -> TermNode -> StateT HasChanged (ExceptT HopuFail (UniqueT IO)) ([Disagreement], HopuSol)
        dispatch l lhs rhs
            | (lambda1, lhs') <- viewNestedNLam lhs
            , (lambda2, rhs') <- viewNestedNLam rhs
            , lambda1 > 0 && lambda2 > 0
            = (\lambda -> dispatch (l + lambda) (makeNestedNLam (lambda1 - lambda) lhs') (makeNestedNLam (lambda2 - lambda) rhs')) $! min lambda1 lambda2
            | (lambda1, lhs') <- viewNestedNLam lhs
            , (rhs_head, rhs_tail) <- unfoldNApp rhs
            , lambda1 > 0 && isRigidAtom rhs_head
            = dispatch (l + lambda1) lhs' (List.foldl' mkNApp (normalizeWithSuspension rhs_head (mkSuspension 0 lambda1 []) HNF) ([ mkSusp rhs_tail_element (mkSuspension 0 lambda1 []) | rhs_tail_element <- rhs_tail ] ++ map mkNIdx [lambda1 - 1, lambda1 - 2 .. 0]))
            | (lhs_head, lhs_tail) <- unfoldNApp lhs
            , (lambda2, rhs') <- viewNestedNLam rhs
            , isRigidAtom lhs_head && lambda2 > 0
            = dispatch (l + lambda2) (List.foldl' mkNApp (normalizeWithSuspension lhs_head (mkSuspension 0 lambda2 []) HNF) ([ mkSusp lhs_tail_element (mkSuspension 0 lambda2 []) | lhs_tail_element <- lhs_tail ] ++ map mkNIdx [lambda2 - 1, lambda2 - 2 .. 0])) rhs'
            | (lhs_head, lhs_tail) <- unfoldNApp lhs
            , (rhs_head, rhs_tail) <- unfoldNApp rhs
            , isRigidAtom lhs_head && isRigidAtom rhs_head
            = if lhs_head == rhs_head && length lhs_tail == length rhs_tail
                then loop ([ (l, lhs' :=?=: rhs') | (lhs', rhs') <- zip lhs_tail rhs_tail ] ++ disagreements) subst labeling
                else lift (throwE RigidRigidFail)
            | (LVar var, parameters) <- unfoldNApp lhs
            , isPatternRespectTo var parameters labeling
            = do
                output <- lift (mksubst var rhs parameters labeling)
                case output of
                    Nothing -> solveNext
                    Just (HopuSol labeling' subst') -> do
                        put True
                        loop (bindVars subst' disagreements) (subst' <> subst) labeling'
            | (LVar var, parameters) <- unfoldNApp rhs
            , isPatternRespectTo var parameters labeling
            = do
                output <- lift (mksubst var lhs parameters labeling)
                case output of
                    Nothing -> solveNext
                    Just (HopuSol labeling' subst') -> do
                        put True
                        loop (bindVars subst' disagreements) (subst' <> subst) labeling'
            | otherwise
            = solveNext
        solveNext :: StateT HasChanged (ExceptT HopuFail (UniqueT IO)) ([Disagreement], HopuSol)
        solveNext = do
            (disagreements', HopuSol labeling' subst') <- loop disagreements mempty labeling
            return (bindVars subst' (makeNestedNLam l lhs :=?=: makeNestedNLam l rhs) : disagreements', HopuSol labeling' (subst' <> subst))

runHOPU :: Labeling -> [Disagreement] -> UniqueT IO (Maybe ([Disagreement], HopuSol))
runHOPU = go where
    loop :: ([Disagreement], HopuSol) -> StateT HasChanged (ExceptT HopuFail (UniqueT IO)) ([Disagreement], HopuSol)
    loop (disagreements, HopuSol labeling subst)
        | null disagreements = return (disagreements, HopuSol labeling subst)
        | otherwise = do
            (disagreements', HopuSol labeling' subst') <- simplify disagreements labeling
            let result = (disagreements', HopuSol labeling' (subst' <> subst))
            has_changed <- get
            if has_changed then put False >> loop result else return result
    go :: Labeling -> [Disagreement] -> UniqueT IO (Maybe ([Disagreement], HopuSol))
    go labeling disagreements = do
        output <- runExceptT (runStateT (loop (disagreements, HopuSol labeling mempty)) False)
        case output of
            Left _ -> return Nothing
            Right (result, _) -> return (Just result)

getLVars :: HasLVar expr => expr -> Set.Set LogicVar
getLVars = flip accLVars Set.empty

flatten :: VarBinding -> TermNode -> TermNode
flatten (VarBinding mapsto) = go . normalize NF where
    go :: TermNode -> TermNode
    go (LVar v) = maybe (mkLVar v) id (Map.lookup v mapsto)
    go (NCon c) = mkNCon c
    go (NIdx i) = mkNIdx i
    go (NApp t1 t2) = mkNApp (go t1) (go t2)
    go (NLam x t) = mkNLam x (go t)

(+->) :: Monad m => LogicVar -> TermNode -> ExceptT HopuFail m VarBinding
v +-> t
    | LVar v == t' = return (VarBinding $! Map.empty)
    | v `Set.member` getLVars t' = throwE OccursCheckFail
    | otherwise = return (VarBinding $! Map.singleton v t')
    where
        t' :: TermNode
        t' = etaReduce (normalize NF t)

getNewLVar :: MonadUnique m => ScopeLevel -> StateT Labeling m TermNode
getNewLVar label = do
    u <- getUnique
    let sym = LVarUnique $! u
    sym `seq` modify (enrollLabel sym label)
    return (mkLVar sym)

readDisagreement :: String -> Disagreement
readDisagreement = final . readEquation where
    usual :: Char -> Bool
    usual c = isUpper c || isLower c || isDigit c || c == '_'
    readVar :: ReadS String
    readVar (c : s)
        | isUpper c = one (c : takeWhile usual s, dropWhile usual s)
    readVar _ = []
    readCon :: ReadS String
    readCon (c : s)
        | isLower c = one (c : takeWhile usual s, dropWhile usual s)
    readCon _ = []
    maximal :: ReadS a -> ReadS [a]
    maximal p s = [ (x : xs, s'') | (x, s') <- p s, (xs, s'') <- maximal p s' ] /> one ([], s)
    readSpace :: ReadS a -> ReadS a
    readSpace p (' ' : s) = p s
    readSpace p _ = []
    readTermNode :: [String] -> Prec -> ReadS TermNode
    readTermNode nms 0 s = [ (mkNLam nm t1, s'') | (nm, '\\' : ' ' : s') <- readVar s, (t1, s'') <- readTermNode (nm : nms) 0 s' ] /> readTermNode nms 1 s
    readTermNode nms 1 s = [ (List.foldl' mkNApp t ts, s'') | (t, s') <- readTermNode nms 2 s, (ts, s'') <- maximal (readSpace (readTermNode nms 2)) s' ]
    readTermNode nms 2 s = [ (maybe (LVar $! LVarNamed v) mkNIdx (v `List.elemIndex` nms), s') | (v, s') <- readVar s ] /> [ (mkNCon $! QualifiedName NoQual c, s') | (c, s') <- readCon s ] /> readTermNode nms 3 s
    readTermNode nms _ ('(' : s) = [ (t, s') | (t, ')' : s') <- readTermNode nms 0 s ]
    readTermNode nms _ _ = []
    readEquation :: ReadS Disagreement
    readEquation s = [ (t1 :=?=: t2, s'') | (t1, ' ' : '~' : ' ' : s') <- readTermNode [] 0 s, (t2, s'') <- readTermNode [] 0 s' ]
    final :: [(Disagreement, String)] -> Disagreement
    final [] = error "readDisagreement: no parse..."
    final [(eqn, "")] = eqn
    final [_] = error "readDisagreement: not EOF..."
    final _ = error "readDisagreement: ambiguous parses..."

instance Labelable Name where
    enrollLabel atom level labeling = labeling { _ConLabel = Map.insert atom level (_ConLabel labeling) }
    updateLabel atom level labeling = labeling { _ConLabel = Map.update (const (Just level)) atom (_ConLabel labeling) }
    lookupLabel atom = maybe (theDefaultLevel atom) id . Map.lookup atom . _ConLabel where
        theDefaultLevel :: Name -> ScopeLevel
        theDefaultLevel (UniquelyGened _ _) = maxBound
        theDefaultLevel (QualifiedName _ _) = 0

instance Labelable LVar where
    enrollLabel atom level labeling = labeling { _VarLabel = Map.insert atom level (_VarLabel labeling) }
    updateLabel atom level labeling = labeling { _VarLabel = Map.update (const (Just level)) atom (_VarLabel labeling) }
    lookupLabel atom = maybe (theDefaultLevel atom) id . Map.lookup atom . _VarLabel where
        theDefaultLevel :: LogicVar -> ScopeLevel
        theDefaultLevel (LVarNamed _) = 0
        theDefaultLevel (LVarUnique _) = maxBound

instance ZonkLVar Labeling where
    zonkLVar subst labeling
        = labeling
            { _VarLabel = Map.fromAscList
                [ mkstrict
                    ( v
                    , foldr min (lookupLabel v labeling)
                        [ level'
                        | (v', t') <- Map.toList mapsto
                        , v `Set.member` getLVars t'
                        , level' <- toList (Map.lookup v' varlabel)
                        ]
                    )
                | v <- Set.toAscList (Map.keysSet mapsto `Set.union` Map.keysSet varlabel)
                ]
            }
        where
            mapsto :: Map.Map LogicVar TermNode
            mapsto = unVarBinding subst
            varlabel :: Map.Map LogicVar ScopeLevel
            varlabel = _VarLabel labeling
            mkstrict :: (LogicVar, ScopeLevel) -> (LogicVar, ScopeLevel)
            mkstrict pair = snd pair `seq` pair

instance HasLVar TermNode where
    accLVars = go . normalize NF where
        go :: TermNode -> Set.Set LogicVar -> Set.Set LogicVar
        go (LVar v) = Set.insert v
        go (NCon c) = id
        go (NIdx i) = id
        go (NApp t1 t2) = go t1 . go t2
        go (NLam x t) = go t
    bindVars = flatten

instance HasLVar a => HasLVar [a] where
    accLVars = flip (foldr accLVars)
    bindVars = map . bindVars

instance HasLVar b => HasLVar (a, b) where
    accLVars = accLVars . snd
    bindVars = fmap . bindVars

instance HasLVar a => HasLVar (Map.Map k a) where
    accLVars = accLVars . Map.elems
    bindVars = Map.map . bindVars

instance Semigroup VarBinding where
    theta2 <> theta1 = VarBinding $! map21 where
        map1 :: Map.Map LogicVar TermNode
        map1 = unVarBinding theta1
        map2 :: Map.Map LogicVar TermNode
        map2 = unVarBinding theta2
        map21 :: Map.Map LogicVar TermNode
        map21 = bindVars theta2 map1 `Map.union` map2

instance Monoid VarBinding where
    mempty = VarBinding $! map0 where
        map0 :: Map.Map LogicVar TermNode
        map0 = Map.empty

instance ZonkLVar VarBinding where
    zonkLVar subst binding = subst <> binding

instance ZonkLVar a => ZonkLVar [a] where
    zonkLVar = map . zonkLVar

instance HasLVar Disagreement where
    accLVars (lhs :=?=: rhs) = accLVars lhs . accLVars rhs
    bindVars theta (lhs :=?=: rhs) = bindVars theta lhs :=?=: bindVars theta rhs

instance ZonkLVar HopuSol where
    zonkLVar subst (HopuSol labeling binding) = HopuSol (zonkLVar subst labeling) (zonkLVar subst binding)

instance Outputable Labeling where
    pprint _ labeling
        = strcat
            [ strstr "Labeling\n"
            , strstr "    { _ConLabel = " . plist 8 [ showName x . strstr " *---> " . shows scp | (x, scp) <- Map.toList (_ConLabel labeling) ] . nl
            , strstr "    , _VarLabel = " . plist 8 [ showLVar x . strstr " *---> " . shows scp | (x, scp) <- Map.toList (_VarLabel labeling) ] . nl
            , strstr "    } "
            ]
        where
            showLVar :: LVar -> ShowS
            showLVar (LVarNamed x) = strstr x
            showLVar (LVarUnique u) = strstr "?V_" . shows (unUnique u)
            showName :: Name -> ShowS
            showName (QualifiedName _ nm) = strstr nm
            showName (UniquelyGened u _) = strstr "#c_" . shows (unUnique u)

instance Outputable VarBinding where
    pprint _ (VarBinding mapsto) = strstr "VarBinding " . plist 4 [ showLVar x . strstr " +-> " . pprint 0 t | (x, t) <- Map.toList mapsto ] where
        showLVar :: LVar -> ShowS
        showLVar (LVarNamed x) = strstr x
        showLVar (LVarUnique u) = strstr "?V_" . shows (unUnique u)

instance Outputable Disagreement where
    pprint prec (lhs :=?=: rhs)
        | prec > 5 = strstr "(" . go . strstr ")"
        | otherwise = go
        where
            go :: ShowS
            go = pprint 0 lhs . strstr " ~ " . pprint 0 rhs
