module SAT (check, Clause,Polarity(..), Assignment) where

import Data.IntMap(IntMap)
import qualified Data.IntMap.Strict as IMap
import qualified Data.IntSet as ISet
import Control.Monad(foldM)
import Control.Applicative(empty)
import Data.Foldable(foldl')
import Data.List(sortBy)
import Data.Function(on)

import Debug.Trace


type Var        = Int
data Polarity   = Negated | Positive deriving (Eq)

-- | A unique idnetifier for a clause.
type ClauseId   = Int

-- | A clause is a disjunction of literals.
type Clause     = IntMap{-Var-} Polarity

data AnnotClause = AnnotClause
  { clauseVars    :: !Clause
  , clauseLearned :: !(Maybe Int)
    -- ^ If learned, then at what time was it born.
  }

-- | A collection of clauses with unique names.
type Clauses    = IntMap{-ClauseId-} AnnotClause

-- | A unit clause is one where all literals except the one specifically
-- called out are known to be false.
data UnitClause = UnitClause {-# UNPACK #-} !Var !Polarity
                             {-# UNPACK #-} !ClauseId !Clause

-- | An assignment keeps track of the current values for variables.
type Assignment = IntMap{-Var-} Bool

-- | A watch list keeps track of which clauses we should check when
-- a variable is assigned.
type WatchList  = IntMap{-Var-} Clauses


-- | Describes how we got to the current state.
-- Each steap contains the previous state and a trace to get it.
data Trace      = GuessTrue {-# UNPACK #-} !Var !State Trace
                  -- ^ Variable we guessed to be true, state before guess

                | Propagate !UnitClause !State Trace
                  -- ^ A variable we because of the given unit clasue.

                | Initial

data PropTodo   = Todo !UnitClause PropTodo
                | NoWork


-- | State which backtrack
data State = State
  { stateAssignment :: !Assignment
  , stateUnit       :: !PropTodo
  , stateVars       :: ![Var]
  }

-- | State that does not backtrack
data PermState = PermState
  { stateNextClause :: !Int
  , stateWatch      :: !WatchList
  , learnCount      :: !Int
  , clauseUseCount  :: !(IntMap{-ClauseId-} Int)
  , varUseCount     :: !(IntMap{-Var-} Int)
  , varOrd          :: ![Var]
  , restartCount    :: !Int
  }


initState :: State
initState = State { stateAssignment = IMap.empty
                  , stateUnit       = NoWork
                  , stateVars       = []
                  }

initPermState :: PermState
initPermState = PermState { stateWatch      = IMap.empty
                          , stateNextClause = 0
                          , learnCount      = 0
                          , clauseUseCount  = IMap.empty
                          , varUseCount     = IMap.empty
                          , varOrd          = []
                          , restartCount    = 1000
                          }


-- | Compute the opposite polarity.
negatePolarity :: Polarity -> Polarity
negatePolarity p =
  case p of
    Negated  -> Positive
    Positive -> Negated

-- | Compute the value of a literal under the given assignment, if any.
literalValue :: Assignment -> Var -> Polarity -> Maybe Bool
literalValue agn x pol =
  do b <- IMap.lookup x agn
     pure $! case pol of
               Positive -> b
               Negated  -> not b


-- | Try to watch the variable of a literal from a clause.
-- Fails if we already have an entry for this clause and this variable.
tryAddWatch :: Var -> ClauseId -> AnnotClause -> WatchList -> Maybe WatchList
tryAddWatch x cid c w = IMap.alterF upd x w
  where
  upd mb =
    case mb of
      Nothing -> pure $! Just $! IMap.singleton cid c
      Just cs ->
        case IMap.insertLookupWithKey (\_ new _ -> new) cid c cs of
          (Nothing,cs1) -> pure $! Just $! cs1
          (Just _,_)    -> empty


-- | Try to move a clause to a new watch location.
-- Conflict and unit clauses are not moved, as well as clauses that
-- have already become true.  Instead, they are added to the set of
-- clauses that will stay on this watch list.
-- New unit clauses are added to the unit clause list.
moveClause :: Assignment -> WatchList -> ClauseId -> AnnotClause -> PropTodo ->
              Either (Maybe PropTodo) WatchList
moveClause agn wl cid c us = findLoc (IMap.toList (clauseVars c)) Nothing
  where
  findLoc ps mb =
    case ps of
      [] -> case mb of
              Nothing -> Left Nothing
              Just u  -> Left (Just (Todo u us))
      (x,pol) : more ->
         case literalValue agn x pol of
           Just True  -> Left Nothing
           Just False -> findLoc more mb
           Nothing ->
             case tryAddWatch x cid c wl of
               Just w1 -> Right w1
               Nothing -> let u = Just $! UnitClause x pol cid $! clauseVars c
                          in u `seq` findLoc more u


-- | Start monitoring different variables of the clauses after assigning
-- the given variable.  Also computes any new unit clauses.
moveClauses ::
  Assignment -> Var -> WatchList -> PropTodo -> (PropTodo,WatchList)
moveClauses agn x wl0 us0 =
  case IMap.lookup x wl0 of
    Nothing   -> (us0, wl0)
    Just todo -> go IMap.empty us0 wl0 (IMap.toList todo)
  where
  go stay us wl todo =
    case todo of
      [] -> let newWs = IMap.insert x stay wl
            in newWs `seq` (us,newWs)
      (cid,c) : more ->
         case moveClause agn wl cid c us of
           Right wl1 -> go stay us wl1 more
           Left mb   ->
             let stay1 = IMap.insert cid c stay
             in case mb of
                  Nothing  -> stay1 `seq` go stay1 us  wl more
                  Just us1 -> stay1 `seq` go stay1 us1 wl more


-- | Set a previously unasigned variable to a given value an
-- move around clauses as needed.
setVar :: Var -> Bool -> PermState -> State -> (PermState,State)
setVar x b ps s =
  let agn      = IMap.insert x b (stateAssignment s)
      (us,ws1) = agn `seq` moveClauses agn x (stateWatch ps) (stateUnit s)
      ps1      = ps { stateWatch = ws1 }
      s1       = s  { stateAssignment = agn, stateUnit = us }
  in ps1 `seq` s1 `seq` (ps1,s1)
{-# INLINE setVar #-}



pickVar :: State -> Maybe (Var,State)
pickVar s = case dropWhile done (stateVars s) of
              []     -> Nothing
              x : xs -> Just (x, s { stateVars = xs })
  where done x = IMap.member x (stateAssignment s)

bumpClauseUseCount :: ClauseId -> PermState -> PermState
bumpClauseUseCount cid ps =
  ps { clauseUseCount = IMap.insertWith (+) cid 1 (clauseUseCount ps) }

bumpVarUseCount :: Clause -> PermState -> PermState
bumpVarUseCount confl ps =
  ps { varUseCount = IMap.unionWith (+) new (varUseCount ps) }
  where
  new = IMap.map (const 1) confl

debugEnd :: PermState -> a -> a
debugEnd ps a =
  trace ("Learned clauses:\n" ++ show (learnCount ps)) $
  trace ("UsedClauses:") $
  trace (unlines $ map show $ IMap.toList learnC) $
  trace ("VarUses:") $
  trace (show (newVarOrder ps)) a
  where
  learnC = foldl' addClauses IMap.empty (stateWatch ps)
  addClauses mp is = IMap.foldlWithKey' addClause mp is
  addClause mp cid an =
    case clauseLearned an of
      Nothing -> mp
      Just born ->
        let life = learnCount ps - born
            uses = IMap.findWithDefault 0 cid (clauseUseCount ps)
        in life `seq` IMap.insert cid (uses,life) mp

newVarOrder :: PermState -> [Var]
newVarOrder ps = map fst
               $ sortBy (compare `on` snd)
               $ IMap.toList
               $ IMap.unionWith max (varUseCount ps) dfltMap
  where
  dfltMap = IMap.fromList [ (v,negate i) | (v,i) <- varOrd ps `zip` [ 0 .. ] ]

forgetLearned :: PermState -> WatchList
forgetLearned ps = IMap.map (IMap.filterWithKey keep) (stateWatch ps)
  where
  keep cid an = case clauseLearned an of
                  Nothing   -> True
                  Just born ->
                    case IMap.lookup cid (clauseUseCount ps) of
                      Just n  -> n > 5 || (learnCount ps - born < 200)
                      Nothing -> False -- ?

restart :: PermState -> State -> Trace -> Maybe Assignment
restart ps sFin tFin = trace "RESTARTING" $ search ps1 s1 Initial
  where
  s0       = back sFin tFin
  ps1      = ps { stateWatch = forgetLearned ps
                , varOrd = newVarOrder ps
                , restartCount = 2 * restartCount ps
                }
  s1       = s0 { stateVars = varOrd ps1 }

  back s t = case t of
               Initial -> s
               GuessTrue _ s1 t1 -> back s1 t1
               Propagate _ s1 t1 -> back s1 t1


search :: PermState -> State -> Trace -> Maybe Assignment
search ps s prev =
  case stateUnit s of

    NoWork -> case pickVar s of
                Nothing     -> debugEnd ps $! Just $! stateAssignment s
                Just (x,s1) -> search ps1 s2 (GuessTrue x s prev)
                  where (ps1,s2) = setVar x True ps s1

    Todo u@(UnitClause x p cid c) us ->
      case literalValue (stateAssignment s) x p of
        Just True  -> search ps s { stateUnit = us } prev
        Just False -> backtrack (bumpClauseUseCount cid ps) prev c
        Nothing -> search (bumpClauseUseCount cid ps1) s1 (Propagate u s prev)
          where (ps1,s1) = b `seq` setVar x b ps s { stateUnit = us }
                b        = p == Positive

backtrack :: PermState -> Trace -> Clause -> Maybe Assignment
backtrack ps steps confl =
  case steps of
    Initial -> debugEnd ps Nothing

    GuessTrue x s more ->

      case IMap.lookup x confl of
        Just Negated ->
          case mbY of
            Nothing -> search ps1 s2 more'
            Just y  -> let ac = AnnotClause
                                  { clauseVars    = confl
                                  , clauseLearned = Just (learnCount ps1)
                                  }
                           ps2 = ac `seq` watchAt x y cid ac ps1
                           newLearnCount = learnCount ps2 + 1
                           ps3 = bumpVarUseCount confl
                                        ps2 { learnCount = newLearnCount }
                       in if True {-newLearnCount < restartCount ps3-}
                              then ps3 `seq` search ps3 s2 more'
                              else restart ps3 s2 more'
          where
          (cid,ps1)      = newClauseId ps
          (mbY,s1,more') = backjump confl s more
          s2             = s1 { stateUnit = Todo
                                              (UnitClause x Negated cid confl)
                                              (stateUnit s1) }

        _ -> backtrack ps more confl

    Propagate (UnitClause x p _ asmps) _ more
      | Just p1 <- IMap.lookup x confl
      , negatePolarity p1 == p ->
          backtrack ps more $! IMap.delete x $! IMap.union asmps confl
      | otherwise -> backtrack ps more confl


backjump :: Clause -> State -> Trace -> (Maybe Var,State,Trace)
backjump confl = go
  where
  go s steps  =
    case steps of
      GuessTrue x s1 more
        | not (x `IMap.member` confl) -> go s1 more
        | otherwise -> (Just x, s, steps)

      Propagate (UnitClause x _ _ _) s1 more
        | not (x `IMap.member` confl) -> go s1 more
        | otherwise -> (Just x, s, steps)

      Initial -> (Nothing, s, steps)



check :: [Clause] -> Maybe Assignment
check cs =
  do (ps,s) <- foldM newClause (ps0,s0) cs
     search ps s Initial
  where
  vs  = ISet.toList (ISet.unions (map IMap.keysSet cs))
  s0  = initState { stateVars = vs }
  ps0 = initPermState { varOrd = vs }

newClauseId :: PermState -> (ClauseId, PermState)
newClauseId s = s1 `seq` (n, s1)
  where n  = stateNextClause s
        s1 = s { stateNextClause = n + 1 }

watchAt :: Var -> Var -> ClauseId -> AnnotClause -> PermState -> PermState
watchAt x y cid c s = s { stateWatch = add x $ add y $ stateWatch s }
  where add v = IMap.insertWith IMap.union v $! IMap.singleton cid c

newClause :: (PermState,State) -> Clause -> Maybe (PermState, State)
newClause (ps,s) c =
  do ((x,p),mp1) <- IMap.minViewWithKey c
     let (cid,ps1) = newClauseId ps
     Just $! case IMap.minViewWithKey mp1 of
               Nothing ->
                 let s1 = s { stateUnit = Todo (UnitClause x p cid c)
                                               (stateUnit s)}
                 in s1 `seq` (ps1,s1)

               Just ((y,_),_) ->
                 let ac  = AnnotClause { clauseVars = c
                                       , clauseLearned = Nothing
                                       }
                     ps2 = ac `seq` watchAt x y cid ac ps1
                 in ps2 `seq` (ps2,s)

