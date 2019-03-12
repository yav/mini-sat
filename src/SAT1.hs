module SAT1 (solver1) where

import Data.Set(Set)
import qualified Data.Set as Set
import Data.Map(Map)
import qualified Data.Map as Map
import Data.Maybe(mapMaybe)
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
                  deriving (Eq,Ord,Show)

data Polarity   = Negated | Positive
                  deriving (Eq,Ord,Show)

data Literal    = Literal { litVar :: {-# UNPACK #-} !Var
                          , litPol ::                !Polarity
                          } deriving (Eq,Ord,Show)

type ClauseId   = Int
data Clause     = Clause { clauseId   :: {-# UNPACK #-} !ClauseId
                         , clauseVars ::                !(Map Var Polarity)
                         } deriving Show

instance Eq Clause where
  c == d = clauseId c == clauseId d

instance Ord Clause where
  compare c d = compare (clauseId c) (clauseId d)

data UnitClause = UnitClause !Literal !Clause
                    deriving Show

type Assignment = Map Var Bool

-- | Describes how we got to the current state.
-- Each steap contains the previous state and a trace to get it.
data Trace      = GuessTrue !Var !State !Trace
                  -- ^ Variable we guessed to be true, state before guess

                | Propagate !(Map Var Polarity) !Literal !State !Trace
                | Initial

type WatchList  = Map Var (Set Clause)



-- | State which backtrack
data State = State
  { stateAssignment :: !Assignment
  , stateUnit       :: ![UnitClause]
  , stateVars       :: ![Var]
  }

-- | State that does not backtrack
data PermState = PermState
  { stateNextClause :: !Int
  , stateWatch      :: !WatchList
  }


initState :: State
initState = State { stateAssignment = Map.empty
                  , stateUnit       = []
                  , stateVars       = []
                  }

initPermState :: PermState
initPermState = PermState { stateWatch      = Map.empty
                          , stateNextClause = 0
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


-- | Try to move a clause to a new watch location.
-- Conflict and unit clauses are not moved, as well as clauses that
-- have already become true.  Instead, they are added to the set of
-- clauses that will stay on this watch list.
-- New unit clauses are added to the unit clause list.
moveClause :: (PermState, State, Set Clause) -> Clause ->
              (PermState, State, Set Clause)
moveClause (ps0,s0,ws) c =
  case Map.foldrWithKey checkLit Nothing (clauseVars c) of
    Nothing -> (ps0,s0,ws1) -- conflict
    Just res -> res

  where
  agn = stateAssignment s0
  wl  = stateWatch ps0
  ws1 = Set.insert c ws

  checkLit x pol mb =
    let l = Literal x pol
    in
    case literalValue agn l of
      Just True  -> Just (ps0,s0,ws1) -- trivially true
      Just False -> mb
      Nothing ->
        case tryAddWatch l c wl of
          Just w1 -> Just (ps0 { stateWatch = w1 }, s0, ws) -- moved
          Nothing ->
            case mb of
              Nothing -> -- unit
                  Just ( ps0
                       , s0 { stateUnit = UnitClause l c : stateUnit s0 }
                       , ws1
                       )
              _ -> mb

-- | Set a previously unasigned variable to a given value an
-- move around clauses as needed.
setVar :: Var -> Bool -> PermState -> State -> (PermState,State)
setVar x b ps s =
  case Map.lookup x (stateWatch ps) of
    Nothing   -> (ps, s')   -- no-one needs updates
    Just todo -> ( ps1 { stateWatch = Map.insert x ws (stateWatch ps1) }
                 , s1
                 )
      where (ps1,s1,ws) = foldl' moveClause (ps,s',Set.empty) todo

  where
  s'       = s { stateAssignment = Map.insert x b (stateAssignment s) }

-- | Set the given literal to True, and move clauses around as needed.
setLitTrue :: Literal -> PermState -> State -> (PermState,State)
setLitTrue l ps s = setVar (litVar l) (litPol l == Positive) ps s

pickVar :: State -> Maybe (Var,State)
pickVar s = case dropWhile done (stateVars s) of
              []     -> Nothing
              x : xs -> Just (x, s { stateVars = xs })
  where done x = x `Map.member` stateAssignment s

search :: PermState -> State -> Trace -> Maybe Assignment
search ps s prev =
  case stateUnit s of

    [] -> case pickVar s of
            Nothing     -> Just (stateAssignment s)
            Just (x,s1) ->  search ps1 s2 (GuessTrue x s prev)
              where (ps1,s2) = setVar x True ps s1

    UnitClause l c : us ->
      case literalValue (stateAssignment s) l of
        Just True  -> search ps s { stateUnit = us } prev
        Just False -> backtrack ps prev (clauseVars c)
        Nothing    -> seq ps1 $ seq s1 $ search ps1 s1 newTr
          where
          newTr     = Propagate (Map.delete (litVar l) (clauseVars c)) l s prev
          (ps1,s1)  = setLitTrue l ps s { stateUnit = us }

backtrack :: PermState -> Trace -> Map Var Polarity -> Maybe Assignment
backtrack ps steps confl =
  case steps of
    Initial -> Nothing

    GuessTrue x s more ->

      case Map.lookup x confl of
        Just Negated ->
          case mbY of
            Nothing -> s2 `seq` search ps1 s2 more'
            Just y ->
              let ps2 = watchAt x y c ps1
              in ps2 `seq` s2 `seq` search ps2 s2 more'

          where
          s2             = s1 { stateUnit = UnitClause (Literal x Negated) c
                                          : stateUnit s1 }
          (mbY,s1,more') = backjump confl s more
          (c,ps1)        = newFreeClause ps (negatePolarity <$> confl)
                                                      -- learned clause

        _ -> backtrack ps more confl


    Propagate asmps l _ more -> backtrack ps more newConfl
      where
      newConfl =
        case Map.lookup (litVar l) confl of
          Just p | negatePolarity p == litPol l -> Map.union asmps confl
          _                                     -> confl

backjump :: Map Var Polarity -> State -> Trace -> (Maybe Var,State,Trace)
backjump confl s steps  =
  case steps of
    GuessTrue x s1 more
      | not (x `Map.member` confl) -> backjump confl s1 more
      | otherwise -> (Just x,s,steps)

    Propagate _ l s1 more
      | not (litVar l `Map.member` confl) -> backjump confl s1 more
      | otherwise -> (Just (litVar l),s,steps)

    Initial -> (Nothing,s,steps)


check :: [Map Var Polarity] -> Maybe Assignment
check cs =
  do (ps,s) <- foldM newClause (initPermState,s0) cs
     search ps s Initial
  where
  s0 = initState { stateVars = Set.toList (Set.unions (map Map.keysSet cs)) }

newFreeClause :: PermState -> Map Var Polarity -> (Clause, PermState)
newFreeClause s lits = c `seq` s1 `seq` (c,s1)
  where n  = stateNextClause s
        c  = Clause { clauseId = n, clauseVars = lits }
        s1 = s { stateNextClause = n + 1 }

watchAt :: Var -> Var -> Clause -> PermState -> PermState
watchAt x y c s = s { stateWatch = add x $ add y $ stateWatch s }
  where add v = Map.insertWith Set.union v (Set.singleton c)

newClause :: (PermState,State) -> Map Var Polarity -> Maybe (PermState, State)
newClause (ps,s) lits =
  do ((x,p),mp1) <- Map.minViewWithKey lits
     let (c,ps1) = newFreeClause ps lits
     case Map.minViewWithKey mp1 of
       Nothing ->
         let newS = s { stateUnit = UnitClause (Literal x p) c : stateUnit s }
         in ps1 `seq` newS `seq` Just (ps1,newS)

       Just ((y,_),_) ->
         let newPS = watchAt x y c ps1
         in newPS `seq` Just (newPS, s)


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


