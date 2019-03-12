module SAT1 (solver1) where

import Data.Set(Set)
import qualified Data.Set as Set
import Data.Map(Map)
import qualified Data.Map as Map
import Data.Maybe(fromMaybe,mapMaybe)
import Data.Foldable(foldl',toList)
import Control.Monad(foldM)

import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import qualified Ersatz.Solution as Ersatz
import qualified Ersatz.Problem as Ersatz
import qualified Ersatz.Internal.Formula as Ersatz



newtype Var     = Var Int
                  deriving (Eq,Ord)

data Polarity   = Negated | Positive
                  deriving (Eq,Ord)

data Literal    = Literal { litVar :: {-# UNPACK #-} !Var
                          , litPol ::                !Polarity
                          } deriving (Eq,Ord)

type ClauseId   = Int
data Clause     = Clause { clauseId   :: {-# UNPACK #-} !ClauseId
                         , clauseVars ::                !(Map Var Polarity)
                         }

instance Eq Clause where
  c == d = clauseId c == clauseId d

instance Ord Clause where
  compare c d = compare (clauseId c) (clauseId d)

data UnitClause = UnitClause !Literal !Clause

type Assignment = Map Var Bool

-- | Describes how we got to the current state.
-- Each steap contains the previous state and a trace to get it.
data Trace      = GuessTrue !Var !State !Trace
                  -- ^ Variable we guessed to be true, state before guess

                | Propagate !(Map Var Polarity) !Literal !State !Trace
                | Initial

type WatchList  = Map Var (Set Clause)



data State = State
  { stateAssignment :: !Assignment
  , stateWatch      :: !WatchList
  , stateUnit       :: ![UnitClause]
  , stateVars       :: ![Var]
  }


initState :: State
initState = State { stateAssignment = Map.empty
                  , stateWatch      = Map.empty
                  , stateUnit       = []
                  , stateVars       = []
                  }


-- | Compute the opposite polarity.
negatePolarity :: Polarity -> Polarity
negatePolarity p =
  case p of
    Negated  -> Positive
    Positive -> Negated

-- | Compute the value of a literal under the given assignment, if any.
literalValue :: Assignment -> Literal -> Maybe Bool
literalValue agn l =
  do b <- Map.lookup (litVar l) agn
     pure $! case litPol l of
               Positive -> b
               Negated  -> not b


-- | Try to watch the variable of a literal from a clause.
-- Fails if we already have an entry for this clause and this variable.
tryAddWatch :: Literal -> Clause -> WatchList -> Maybe WatchList
tryAddWatch l c w = Map.alterF upd x w
  where
  x = litVar l
  upd mb =
    case mb of
      Nothing -> Just $! Just $! Set.singleton c
      Just cs
        | c `Set.member` cs -> Nothing
        | otherwise         -> Just $! Just $! Set.insert c cs


-- | Add a clause to a new watch list, or move it to the unit clause list.
watchClause :: State -> Clause -> State
watchClause s0 c = fromMaybe s0
                 $ Map.foldrWithKey checkLit Nothing (clauseVars c)
  {- If we fail to find an unassigned variable, then we do nothing.
     The reason is that the clause must already be on the unit-clause list,
     and therefore we'll spot the conflict when we get to it. -}
  where
  agn = stateAssignment s0
  wl  = stateWatch s0

  checkLit x pol mb =
    let l = Literal x pol
    in
    case literalValue agn l of
      Just True  -> Just $! s0
      Just False -> mb
      Nothing ->
        case tryAddWatch l c wl of
          Just w1 -> Just $! s0 { stateWatch = w1 }
          Nothing ->
            case mb of
              Nothing ->
                  Just $! s0 { stateUnit = UnitClause l c : stateUnit s0 }
              _ -> mb

-- | Set a previously unasigned variable to a given value an
-- move around clauses as needed.
setVar :: Var -> Bool -> State -> State
setVar x b s =
  case wat of
    Nothing   -> s'                         -- Nothing to watch
    Just todo -> foldl' watchClause s' todo -- Update watched
  where
  (wat,w1) = Map.updateLookupWithKey (\_ _ -> Nothing) x (stateWatch s)
  s'       = s { stateAssignment = Map.insert x b (stateAssignment s)
               , stateWatch      = w1
               }

-- | Set the given literal to True, and move clauses around as needed.
setLitTrue :: Literal -> State -> State
setLitTrue l = setVar (litVar l) (litPol l == Positive)

pickVar :: State -> Maybe (Var,State)
pickVar s = case dropWhile done (stateVars s) of
              []     -> Nothing
              x : xs -> Just (x, s { stateVars = xs })
  where done x = x `Map.member` stateAssignment s

search :: State -> Trace -> Maybe Assignment
search s prev =
  case stateUnit s of

    [] -> case pickVar s of
            Nothing     -> Just (stateAssignment s)
            Just (x,s1) -> search (setVar x True s1) (GuessTrue x s prev)

    UnitClause l c : us ->
      case literalValue (stateAssignment s) l of
        Just True  -> search s { stateUnit = us } prev
        Just False -> backtrack prev (clauseVars c)
        Nothing    -> search s1 newTr
          where
          newTr = Propagate (Map.delete (litVar l) (clauseVars c)) l s prev
          s1    = setLitTrue l s { stateUnit = us }

backtrack :: Trace -> Map Var Polarity -> Maybe Assignment
backtrack steps confl =
  case steps of
    Initial -> Nothing

    GuessTrue x s more ->

      case Map.lookup x confl of
        -- XXX: Also add a learned clause here
        Just Negated -> search s2 newTr
          where
          (s1,more') = backjump confl s more
          s2    = setVar x False s1
          newTr = Propagate (Map.delete x confl) (Literal x Negated) s1 more'

        _ -> backtrack more confl


    Propagate asmps l _ more -> backtrack more newConfl
      where
      newConfl =
        case Map.lookup (litVar l) confl of
          Just p | negatePolarity p == litPol l -> Map.union asmps confl
          _                                     -> confl

backjump :: Map Var Polarity -> State -> Trace -> (State,Trace)
backjump confl s steps  =
  case steps of
    GuessTrue x s1 more
      | not (x `Map.member` confl) -> backjump confl s1 more

    Propagate _ l s1 more
      | not (litVar l `Map.member` confl) -> backjump confl s1 more

    _ -> (s,steps)


check :: [Map Var Polarity] -> Maybe Assignment
check cs =
  do (_,s) <- foldM mk (0,s0) cs
     search s Initial
  where
  s0 = initState { stateVars = Set.toList (Set.unions (map Map.keysSet cs)) }
  mk (n,s) mp =
    do ((x,p),mp1) <- Map.minViewWithKey mp
       let c = Clause { clauseId = n
                      , clauseVars = mp
                      }
           n1 = n + 1
           s1 = case Map.minViewWithKey mp1 of
                  Nothing ->
                    s { stateUnit = UnitClause (Literal x p) c : stateUnit s }
                  Just ((y,_),_) ->
                    s { stateWatch = Map.insertWith Set.union
                                      x (Set.singleton c)
                                   $ Map.insertWith Set.union
                                      y (Set.singleton c)
                                   $ stateWatch s }
       n1 `seq` s1 `seq` Just (n1,s1)


solver1 :: Ersatz.Solver Ersatz.SAT IO
solver1 (Ersatz.SAT n f _) =
  do putStrLn ("Variables: " ++ show n)
     let cs = mapMaybe toCl (toList (Ersatz.formulaSet f))
     putStrLn ("Clauses: " ++ show (length cs))
     case check cs of
       Nothing -> return (Ersatz.Unsatisfied, IntMap.empty)
       Just xs -> return (Ersatz.Satisfied, toSln xs)
  where
  toCl :: Ersatz.Clause -> Maybe (Map Var Polarity)
  toCl cl = let c  = Ersatz.clauseSet cl
                vs = abs `IntSet.map` c
            in if IntSet.size vs == IntSet.size c
                  then Just (toMp c)
                  else Nothing

  toMp :: IntSet -> Map Var Polarity
  toMp = Map.fromList . map toEntry . IntSet.toList

  toEntry :: Int -> (Var,Polarity)
  toEntry x = (Var (abs x), if x > 0 then Positive else Negated)

  toSln :: Assignment -> IntMap Bool
  toSln agn = IntMap.fromList [ (x,b) | (Var x,b) <- Map.toList agn ]


