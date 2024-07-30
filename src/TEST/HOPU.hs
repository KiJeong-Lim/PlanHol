module TEST.HOPU where

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
import HOL.Back.TermNode
import HOL.Front.Ast
import Z.Algo.Function
import Z.Utils

infix 4 +->

infix 6 :=?=:

type Constant = Name

type LogicVar = LVar

type ScopeLevel = Int

type LVarSubst = VarBinding

data Labeling
    = Labeling
        { _ConLabel :: Map.Map Constant ScopeLevel
        , _VarLabel :: Map.Map LogicVar ScopeLevel
        }
    deriving (Eq, Ord, Show)

data Disagreement
    = TermNode :=?=: TermNode
    deriving (Eq, Ord, Show)

newtype VarBinding
    = VarBinding { unVarBinding :: Map.Map LogicVar TermNode }
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

class Labelable atom where
    enrollLabel :: atom -> ScopeLevel -> Labeling -> Labeling
    updateLabel :: atom -> ScopeLevel -> Labeling -> Labeling
    lookupLabel :: atom -> Labeling -> ScopeLevel

class HasLVar expr where
    accLVars :: expr -> Set.Set LogicVar -> Set.Set LogicVar
    bindVars :: VarBinding -> expr -> expr

class ZonkLVar expr where
    zonkLVar :: LVarSubst -> expr -> expr

testHOPU :: IO ()
testHOPU = go (Labeling { _ConLabel = Map.empty, _VarLabel = Map.empty }) [] where
    go :: Labeling -> [Disagreement] -> IO ()
    go labeling disagrees = do
        s <- getLine
        case words s of
            [] -> putStrLn "quit"
            ["add ", "var", var, level] -> go (enrollLabel (LVarNamed $! var) (read level) labeling) disagrees
            ["add ", "con", con, level] -> go (enrollLabel (QualifiedName NoQual $! con) (read level) labeling) disagrees
            ["add ", "eqn", eqn] -> do
                eqn <- return $! readDisagreement eqn
                go labeling (eqn : disagrees)
            ["solve"] -> do
                res <- execUniqueT (runHOPU labeling disagrees)
                case res of
                    Nothing -> putStrLn "no solution..."
                    Just (disagrees', HopuSol labeling mgu) -> do
                        putStrLn ("leftDisagreements = " ++ plist 4 (map (pprint 0) disagrees') "")
                        putStrLn ("finalLabeling = " ++ pprint 0 labeling "")
                        putStrLn ("mostGeneralUnifier = " ++ pprint 0 mgu "")
            _ -> go labeling disagrees

runHOPU :: MonadUnique m => Labeling -> [Disagreement] -> m (Maybe ([Disagreement], HopuSol))
runHOPU labeling disagrees = return (Just (disagrees, HopuSol labeling mempty))

theDefaultLevel :: Name -> ScopeLevel
theDefaultLevel (UniquelyGened _ _) = maxBound
theDefaultLevel (QualifiedName _ _) = 0

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
    | LVar v' <- t', LVarNamed {} <- v' = return (VarBinding $! Map.singleton v' (mkLVar v))
    | otherwise = return (VarBinding $! Map.singleton v t')
    where
        t' :: TermNode
        t' = normalize NF t

getNewLVar :: MonadUnique m => ScopeLevel -> StateT Labeling m TermNode
getNewLVar label = do
    u <- getUnique
    let sym = LVarUnique $! u
    sym `seq` modify (enrollLabel sym label)
    return (mkLVar sym)

readDisagreement :: String -> Disagreement
readDisagreement = mkDisagreement . readEquation where
    usual :: Char -> Bool
    usual c = isUpper c || isLower c || isDigit c || c == '_'
    readVar :: ReadS String
    readVar (c : s) = if c `elem` ['A' .. 'Z'] then one (c : takeWhile usual s, dropWhile usual s) else []
    readVar _ = []
    readCon :: ReadS String
    readCon (c : s) = if c `elem` ['a' .. 'z'] then one (c : takeWhile usual s, dropWhile usual s) else []
    readCon _ = []
    maximal :: ReadS a -> ReadS [a]
    maximal p s = [ (x : xs, s'') | (x, s') <- p s, (xs, s'') <- maximal p s' ] /> one ([], s)
    readSpace :: ReadS a -> ReadS a
    readSpace p (' ' : s) = p s
    readSpace _ _ = []
    readTermNode :: [String] -> Prec -> ReadS TermNode
    readTermNode nms 0 s = [ (mkNLam nm t1, s'') | (nm, '\\' : ' ' : s') <- readVar s, (t1, s'') <- readTermNode (nm : nms) 0 s' ] /> readTermNode nms 1 s
    readTermNode nms 1 s = [ (List.foldl' mkNApp ty tys, s'') | (ty, s') <- readTermNode nms 2 s, (tys, s'') <- maximal (readSpace (readTermNode nms 2)) s' ]
    readTermNode nms 2 s = [ (maybe (LVar $! LVarNamed v) mkNIdx (v `List.elemIndex` nms), s') | (v, s') <- readVar s ] /> [ (mkNCon $! QualifiedName NoQual tc, s') | (tc, s') <- readCon s ] /> readTermNode nms 3 s 
    readTermNode nms _ ('(' : s) = [ (t, s') | (t, ')' : s') <- readTermNode nms 0 s ]
    readTermNode nms _ _ = []
    readEquation :: ReadS Disagreement
    readEquation s = [ (t1 :=?=: t2, s'') | (t1, ' ' : ':' : '=' : '?' : '=' : ':' : ' ' : s') <- readTermNode [] 0 s, (t2, s'') <- readTermNode [] 0 s' ]
    mkDisagreement :: [(Disagreement, String)] -> Disagreement
    mkDisagreement [] = error "mkDisagreement: no parse..."
    mkDisagreement [(disagrees, "")] = disagrees
    mkDisagreement [_] = error "mkDisagreement: not EOF..."
    mkDisagreement x = error "mkDisagreement: ambiguous parses..."

instance Labelable Constant where
    enrollLabel atom level labeling = labeling { _ConLabel = Map.insert atom level (_ConLabel labeling) }
    updateLabel atom level labeling = labeling { _ConLabel = Map.update (const (Just level)) atom (_ConLabel labeling) }
    lookupLabel atom = maybe (theDefaultLevel atom) id . Map.lookup atom . _ConLabel

instance Labelable LogicVar where
    enrollLabel atom level labeling = labeling { _VarLabel = Map.insert atom level (_VarLabel labeling) }
    updateLabel atom level labeling = labeling { _VarLabel = Map.update (const (Just level)) atom (_VarLabel labeling) }
    lookupLabel atom = maybe maxBound id . Map.lookup atom . _VarLabel

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
    accLVars (LVar v) = Set.insert v
    accLVars (NCon c) = id
    accLVars (NIdx i) = id
    accLVars (NApp t1 t2) = accLVars t1 . accLVars t2
    accLVars (NLam x t) = accLVars t
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
    theta2 <> theta1 = map21 `seq` VarBinding map21 where
        map1 :: Map.Map LogicVar TermNode
        map1 = unVarBinding theta1
        map2 :: Map.Map LogicVar TermNode
        map2 = unVarBinding theta2
        map21 :: Map.Map LogicVar TermNode
        map21 = bindVars theta2 map1 `Map.union` map2

instance Monoid VarBinding where
    mempty = map0 `seq` VarBinding map0 where
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
            , strstr "    }"
            ]
        where
            showLVar :: LVar -> ShowS
            showLVar (LVarNamed x) = strstr x
            showLVar (LVarUnique u) = strstr "?X_" . shows (unUnique u)
            showName :: Name -> ShowS
            showName (QualifiedName _ nm) = strstr nm
            showName (UniquelyGened u _) = strstr "#c_" . shows (unUnique u)

instance Outputable VarBinding where
    pprint _ (VarBinding mapsto) = strstr "VarBinding " . plist 4 [ showLVar x . strstr " +-> " . pprint 0 t | (x, t) <- Map.toList mapsto ] where
        showLVar :: LVar -> ShowS
        showLVar (LVarNamed x) = strstr x
        showLVar (LVarUnique u) = strstr "?X_" . shows (unUnique u)

instance Outputable Disagreement where
    pprint prec (lhs :=?=: rhs)
        | prec > 5 = strstr "(" . go . strstr ")"
        | otherwise = go
        where
            go :: ShowS
            go = pprint 0 lhs . strstr " :=?=: " . pprint 0 rhs
