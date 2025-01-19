-- Thanks to EatChangmyeong
module PGS.Util where

import Data.Maybe (mapMaybe, isNothing, listToMaybe)
import Data.Tuple (swap)
import Data.List (intercalate, uncons)
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.IntSet as IntSet
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import qualified Data.Map.Merge.Strict as MapMerge
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import Control.Monad (guard)
import Z.Utils

type LRItemSet terminal nonterminal = Map (LRItem terminal nonterminal) (Set [terminal]) -- LR(n) item set with mapping to lookahead sets

type LRAutomaton terminal nonterminal = IntMap (LRState terminal nonterminal) -- LR(n) automaton

data Symbol terminal nonterminal
    = TSym (terminal)
    | NSym (nonterminal)
    deriving (Eq, Ord, Show)

data Rule terminal nonterminal
    = Rule
        { lhs :: nonterminal -- LHS of the rule
        , rhs :: [Symbol terminal nonterminal] -- RHS of the rule, ordered list of 0 or more symbols
        }
    deriving (Eq, Ord, Show)

data CFG terminal nonterminal
    = CFG
        { start :: nonterminal -- starting symbol
        , rules :: IntMap (Rule terminal nonterminal) -- set of rules
        }
    deriving (Eq, Ord, Show)

data LRItem terminal nonterminal -- single LR(0) item
    = LRItem
        { rule :: Int -- zero-based rule number from CFG
        , handle :: Int -- zero-based position of handle
        }
    deriving (Eq, Ord, Show)

data LRState terminal nonterminal
    = LRState
        { kernel :: LRItemSet terminal nonterminal
            -- "kernel" is the item subset that "initiates" the full item set, whose elements are either:
            -- * "genesis" items in the starting state, whose lhs is starting symbol and has zero handle position
            -- * "shifted" items with nonzero handle position
        , transition :: Map (Symbol terminal nonterminal) Int
            -- Index of the next state when shifted by a symbol
        }
    deriving (Eq, Ord, Show)

data Action -- Possible entries in the ACTION table
    = Shift -- shift targets are described in the GOTO table
    | Reduce Int
    | Accept
    | Conflict [Action]
    deriving (Eq, Ord, Show)

data LRTable terminal nonterminal -- LR(n) parsing table
    = LRTable
        { lookahead :: Int -- lookahead length
        , reduceLUT :: IntMap (nonterminal, Int) -- ruleset information for reduction
        , action :: Map (Int, [terminal]) Action -- ACTION table
        , goto :: Map (Int, Symbol terminal nonterminal) Int -- GOTO table
        }
    deriving (Eq, Show)

data ParseTree terminal nonterminal -- parse tree
    = Terminal terminal
    | Nonterminal nonterminal [ParseTree terminal nonterminal]
    deriving (Show)

fixpointWithInit :: Eq a => (a -> a) -> a -> a
-- fixpoint combinator based on `==`
-- `fixpointWithInit f x` terminates only if `f^n x == f (f^n x)` for some `n`
fixpointWithInit f x = let x' = f x in if x == x' then x' else fixpointWithInit f x'

unionItemSet :: Ord terminal => LRItemSet terminal nonterminal -> LRItemSet terminal nonterminal -> LRItemSet terminal nonterminal
-- `Set.union` but for item sets
unionItemSet = Map.unionWith Set.union

unionsItemSet :: (Ord terminal, Foldable foldable) => foldable (LRItemSet terminal nonterminal) -> LRItemSet terminal nonterminal
-- `Set.unions` but for item sets
unionsItemSet = Map.unionsWith Set.union

excludeItemSet :: Ord terminal => LRItemSet terminal nonterminal -> LRItemSet terminal nonterminal -> LRItemSet terminal nonterminal
-- `Set.\\` but for item sets
excludeItemSet = MapMerge.merge MapMerge.preserveMissing' MapMerge.dropMissing $ MapMerge.zipWithMaybeMatched $ go where
    go _ xs ys = let zs = xs Set.\\ ys in zs <$ guard (not $ Set.null zs)

mapMaybeKeys :: Ord b => (a -> Maybe b) -> Map a c -> Map b c
-- `Map.mapMaybe` but with keys
mapMaybeKeys f = Map.fromList . mapMaybe (\(k, v) -> flip (,) v <$> f k) . Map.toList
