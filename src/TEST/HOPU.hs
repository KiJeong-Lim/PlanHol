module TEST.HOPU where

import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.State.Strict
import Control.Monad.Trans.Writer
import HOL.Back.TermNode
import HOL.Front.Ast
import Data.Foldable
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
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

class Labelable atom where
    enrollLabel :: atom -> ScopeLevel -> Labeling -> Labeling
    updateLabel :: atom -> ScopeLevel -> Labeling -> Labeling
    lookupLabel :: atom -> Labeling -> ScopeLevel

class HasLVar expr where
    accFreeLVars :: expr -> Set.Set LogicVar -> Set.Set LogicVar
    applyBinding :: VarBinding -> expr -> expr

class ZonkLVar expr where
    zonkLVar :: LVarSubst -> expr -> expr

theDefaultLevel :: Name -> ScopeLevel
theDefaultLevel (UniquelyGened _ _) = maxBound
theDefaultLevel (QualifiedName _ _) = 0

getFreeLVs :: HasLVar expr => expr -> Set.Set LogicVar
getFreeLVs = flip accFreeLVars Set.empty

flatten :: VarBinding -> TermNode -> TermNode
flatten (VarBinding mapsto) = go . normalize NF where
    go :: TermNode -> TermNode
    go (LVar v) = maybe (mkLVar v) id (Map.lookup v mapsto)
    go (NCon c) = mkNCon c
    go (NIdx i) = mkNIdx i
    go (NApp t1 t2) = mkNApp (go t1) (go t2)
    go (NLam x t) = mkNLam x (go t)

(+->) :: LogicVar -> TermNode -> Maybe VarBinding
v +-> t
    | LVar v == t' = return (VarBinding Map.empty)
    | v `Set.member` getFreeLVs t' = Nothing
    | LVar v' <- t', LVarNamed {} <- v' = return (VarBinding (Map.singleton v' (LVar v)))
    | otherwise = return (VarBinding (Map.singleton v t'))
    where
        t' :: TermNode
        t' = normalize NF t

getNewLVar :: MonadUnique m => ScopeLevel -> StateT Labeling m TermNode
getNewLVar label = do
    u <- getUnique
    let sym = LVarUnique $! u
    sym `seq` modify (enrollLabel sym label)
    return (mkLVar sym)

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
                        , v `Set.member` getFreeLVs t'
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
    accFreeLVars (LVar v) = Set.insert v
    accFreeLVars (NCon c) = id
    accFreeLVars (NIdx i) = id
    accFreeLVars (NApp t1 t2) = accFreeLVars t1 . accFreeLVars t2
    accFreeLVars (NLam x t) = accFreeLVars t
    applyBinding = flatten

instance HasLVar a => HasLVar [a] where
    accFreeLVars = flip (foldr accFreeLVars)
    applyBinding = map . applyBinding

instance HasLVar b => HasLVar (a, b) where
    accFreeLVars = accFreeLVars . snd
    applyBinding = fmap . applyBinding

instance HasLVar a => HasLVar (Map.Map k a) where
    accFreeLVars = accFreeLVars . Map.elems
    applyBinding = Map.map . applyBinding

instance Semigroup VarBinding where
    theta2 <> theta1 = map21 `seq` VarBinding map21 where
        map1 :: Map.Map LogicVar TermNode
        map1 = unVarBinding theta1
        map2 :: Map.Map LogicVar TermNode
        map2 = unVarBinding theta2
        map21 :: Map.Map LogicVar TermNode
        map21 = applyBinding theta2 map1 `Map.union` map2

instance Monoid VarBinding where
    mempty = map0 `seq` VarBinding map0 where
        map0 :: Map.Map LogicVar TermNode
        map0 = Map.empty

instance ZonkLVar VarBinding where
    zonkLVar subst binding = subst <> binding

instance ZonkLVar a => ZonkLVar [a] where
    zonkLVar = map . zonkLVar

instance Outputable Labeling where
    pprint _ labeling
        = strcat
            [ strstr "Labeling\n"
            , strstr "    { _ConLabel = " . strcat [ showName x . strstr " *--- " . shows scp | (x, scp) <- Map.toList (_ConLabel labeling) ] . nl
            , strstr "    , _VarLabel = " . strcat [ showLVar x . strstr " *--- " . shows scp | (x, scp) <- Map.toList (_VarLabel labeling) ] . nl
            , strstr "    }\n"
            ]
        where
            showLVar :: LVar -> ShowS
            showLVar (LVarNamed x) = strstr x
            showLVar (LVarUnique u) = strstr "?X_" . shows (unUnique u)
            showName :: Name -> ShowS
            showName (QualifiedName _ nm) = strstr nm
            showName (UniquelyGened u _) = strstr "c_" . shows (unUnique u)

instance Outputable VarBinding where
    pprint _ (VarBinding mapsto) = strstr "VarBinding" . plist 4 [ showLVar x . strstr " +-> " . pprint 0 t | (x, t) <- Map.toList mapsto ] where
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
