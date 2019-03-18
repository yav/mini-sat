module SAT (check, Clause,Polarity(..), Assignment) where

import Data.IntMap(IntMap)
import qualified Data.IntMap.Strict as IMap
import qualified Data.IntSet as ISet
import Control.Monad(foldM)
import Control.Applicative(empty)


type Var        = Int
data Polarity   = Negated | Positive deriving (Eq)

-- | A unique idnetifier for a clause.
type ClauseId   = Int

-- | A clause is a disjunction of literals.
type Clause     = IntMap{-Var-} Polarity

-- | A collection of clauses with unique names.
type Clauses    = IntMap{-ClauseId-} Clause

-- | A unit clause is one where all literals except the one specifically
-- called out are known to be false.
data UnitClause = UnitClause {-# UNPACK #-} !Var !Polarity !Clause

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
  }


initState :: State
initState = State { stateAssignment = IMap.empty
                  , stateUnit       = NoWork
                  , stateVars       = []
                  }

initPermState :: PermState
initPermState = PermState { stateWatch      = IMap.empty
                          , stateNextClause = 0
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
tryAddWatch :: Var -> ClauseId -> Clause -> WatchList -> Maybe WatchList
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
moveClause :: Assignment -> WatchList -> ClauseId -> Clause -> PropTodo ->
              Either (Maybe PropTodo) WatchList
moveClause agn wl cid c us = findLoc (IMap.toList c) Nothing
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
               Nothing -> let u = Just $! UnitClause x pol c
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

search :: PermState -> State -> Trace -> Maybe Assignment
search ps s prev =
  case stateUnit s of

    NoWork -> case pickVar s of
                Nothing     -> Just $! stateAssignment s
                Just (x,s1) -> search ps1 s2 (GuessTrue x s prev)
                  where (ps1,s2) = setVar x True ps s1

    Todo u@(UnitClause x p c) us ->
      case literalValue (stateAssignment s) x p of
        Just True  -> search ps s { stateUnit = us } prev
        Just False -> backtrack ps prev c
        Nothing    -> search ps1 s1 (Propagate u s prev)
          where (ps1,s1) = b `seq` setVar x b ps s { stateUnit = us }
                b        = p == Positive

backtrack :: PermState -> Trace -> Clause -> Maybe Assignment
backtrack ps steps confl =
  case steps of
    Initial -> Nothing

    GuessTrue x s more ->

      case IMap.lookup x confl of
        Just Negated ->
          case mbY of
            Nothing -> search ps1 s2 more'
            Just y  -> let ps2 = watchAt x y cid confl ps1
                        in ps2 `seq` search ps2 s2 more'
          where
          (cid,ps1)      = newClauseId ps
          (mbY,s1,more') = backjump confl s more
          s2             = s1 { stateUnit = Todo (UnitClause x Negated confl)
                                                 (stateUnit s1) }

        _ -> backtrack ps more confl

    Propagate (UnitClause x p asmps) _ more
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

      Propagate (UnitClause x _ _) s1 more
        | not (x `IMap.member` confl) -> go s1 more
        | otherwise -> (Just x, s, steps)

      Initial -> (Nothing, s, steps)



check :: [Clause] -> Maybe Assignment
check cs =
  do (ps,s) <- foldM newClause (initPermState,s0) cs
     search ps s Initial
  where
  s0 = initState { stateVars = ISet.toList (ISet.unions (map IMap.keysSet cs)) }

newClauseId :: PermState -> (ClauseId, PermState)
newClauseId s = s1 `seq` (n, s1)
  where n  = stateNextClause s
        s1 = s { stateNextClause = n + 1 }

watchAt :: Var -> Var -> ClauseId -> Clause -> PermState -> PermState
watchAt x y cid c s = s { stateWatch = add x $ add y $ stateWatch s }
  where add v = IMap.insertWith IMap.union v $! IMap.singleton cid c

newClause :: (PermState,State) -> Clause -> Maybe (PermState, State)
newClause (ps,s) c =
  do ((x,p),mp1) <- IMap.minViewWithKey c
     let (cid,ps1) = newClauseId ps
     Just $! case IMap.minViewWithKey mp1 of
               Nothing ->
                 let s1 = s { stateUnit = Todo (UnitClause x p c) (stateUnit s)}
                 in s1 `seq` (ps1,s1)

               Just ((y,_),_) ->
                 let ps2 = watchAt x y cid c ps1
                 in ps2 `seq` (ps2,s)

--------------------------------------------------------------------------------


showLit :: Var -> Polarity -> String
showLit x p = shP ++ show x
  where shP = case p of
                Positive -> "+"
                Negated  -> "-"

showClause :: Clause -> String
showClause = unwords . map (uncurry showLit) . IMap.toList

checkUnit :: Assignment -> UnitClause -> UnitClause
checkUnit agn u@(UnitClause x _ c)
  | null bad = u
  | otherwise = error ("Invalid unit clause: " ++ unwords bad)
  where
  bad = [ showLit v p ++ " = " ++ show val ++ ";" | (v,p) <- IMap.toList c
        , v /= x
        , let val = literalValue agn v p
        , val /= Just False ]




