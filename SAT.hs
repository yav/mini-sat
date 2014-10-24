{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE BangPatterns    #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}  -- For unboxed arrays of literals
module SAT where

import qualified Data.Map as Map
import           Data.Map ( Map )
import           Data.Set ( Set )
import qualified Data.Set as Set
import           Data.Sequence (Seq, ViewL(..), (|>), (><))
import qualified Data.Sequence as Seq
import           Data.Array.Unboxed ( IArray, UArray, listArray, rangeSize )
import qualified Data.Array.Unboxed as Arr
import           Data.Maybe ( listToMaybe )

--------------------------------------------------------------------------------
-- Variables and Literals
--------------------------------------------------------------------------------

newtype Variable    = Var Int
                      deriving (Eq,Ord,Show,Read)

newtype Literal     = Lit Int
                      deriving (Eq,Ord,Show,Read,IArray UArray)

-- | Create a new variable.  Variables should be strictly positive.
var :: Int -> Maybe Variable
var x = if x > 0 then Just (Var x) else Nothing

-- | Convert a variable to the corresponding literal.
lit :: Variable -> Literal
lit (Var x) = Lit x

-- | Negate a literal.
litNeg :: Literal -> Literal
litNeg (Lit x) = Lit (negate x)

-- | Access the variable for a literal.
litVar :: Literal -> Variable
litVar (Lit x) = Var (abs x)

-- | Is this literal positive (i.e., a non-negated variable).
litIsPos :: Literal -> Bool
litIsPos (Lit x) = x > 0



--------------------------------------------------------------------------------
-- Clauses
--------------------------------------------------------------------------------

-- | A "list" of literals.
newtype Clause  = Cla (UArray Int Literal)

-- | Create a clause from the list of literals.
-- Returns 'Nothing' if the clause is trivially true.
claFromList :: [Literal] -> Maybe Clause
claFromList = go 0 Set.empty
  where
  go !len seen [] = Just $ Cla $ listArray (0,len-1) $ Set.toList seen
  go !len seen (x : xs)
    | x        `Set.member` seen  = go len seen xs
    | litNeg x `Set.member` seen  = Nothing
    | otherwise                   = go (len + 1) (Set.insert x seen) xs

-- | Is this a false (i.e., empty) clause.
claIsFalse :: Clause -> Bool
claIsFalse (Cla mp) = rangeSize (Arr.bounds mp) == 0

-- | Fine a literal, whose variable satisfies the condition.
claFindLit :: (Variable -> Bool) -> Clause -> Maybe Literal
claFindLit isOk (Cla mp) = listToMaybe $ filter (isOk . litVar) $ Arr.elems mp

-- | If the clause is the reason for the literal to become true,
-- then all other literals must have been false.
claReasonFor :: Literal -> Clause -> [Literal]
claReasonFor l (Cla mp) = [ litNeg l1 | l1 <- Arr.elems mp, l1 /= l ]

-- | If the clause became false, then all its literals must be false.
claReason :: Clause -> [Literal]
claReason (Cla mp) = [ litNeg l | l <- Arr.elems mp ]



--------------------------------------------------------------------------------
-- Assignments
--------------------------------------------------------------------------------

-- | An assignment keeps track of the current values for variables,
-- also keeping track with how these assignments came to be.
data Assignment = Assignment
  { assignVars  :: !(Map Variable AssignInfo)
    -- ^ Bindings for variables, with information about how they came to be.

  , assignTrace :: [[Literal]]
    -- ^ The order in which we assigned the variables (most recent first).
    -- The literals are grouped by decision level.

  , assignDecisionLevel :: !Int
    -- ^ The current decision level, which should match the length of
    -- 'assignTrace'.
  }

-- | Information for a single variable.
data AssignInfo = AssignInfo
  { assignValue     :: Bool         -- ^ Assignment value.
  , assignImpliedBy :: Maybe Clause -- ^ Reason, if implied by a clause.
  , assignAtLevel   :: Int          -- ^ Decision level: 0 top-level,
                                    --   otherwise guess number.
  }

-- | Is the variable defined by the assignment.
assignDefines :: Variable -> Assignment -> Bool
assignDefines x Assignment { .. } = x `Map.member` assignVars

-- | Get the value of the literal under the assignment.
assignGetLit :: Literal -> Assignment -> Maybe Bool
assignGetLit l Assignment { .. } =
  do AssignInfo { .. } <- Map.lookup (litVar l) assignVars
     if litIsPos l then return assignValue
                   else return (not assignValue)

-- | At which decision level, if any, was this variable assigned.
assignGetLevel :: Variable -> Assignment -> Maybe Int
assignGetLevel x Assignment { .. } =
  do AssignInfo { .. } <- Map.lookup x assignVars
     return assignAtLevel

-- | Record the fact that the literal became true.
assignSetLit :: Literal         -- ^ This lieteral became true
             -> Maybe Clause    -- ^ Implied by a clause
             -> Assignment      -- ^ Assignment to modify.
             -> Assignment
assignSetLit l assignImpliedBy Assignment { .. } =
  Assignment { assignVars  = Map.insert (litVar l) info assignVars
             , assignTrace = case assignTrace of
                               -- No need to record top-level assignments.
                               []        -> []
                               ls : more -> (l : ls) : more
             , ..
             }
  where
  info = AssignInfo { assignValue = litIsPos l
                    , assignAtLevel = assignDecisionLevel
                    , .. }

{- | Undo last assignment in the current decision level, if any.
Returns that literal that became true, information about what caused
the assignment, and the modified assignment.
PRE: This is called only when there is something to undo
      (i.e., level is > 0, and there is at least one decision) -}
assignUndoLast :: Assignment -> (Literal, AssignInfo, Assignment)
assignUndoLast Assignment { .. } =
  case assignTrace of
    (l : ls) : lss ->
      case Map.updateLookupWithKey (\_ _ -> Nothing) (litVar l) assignVars of
        (Just i, mp1) -> (l, i, Assignment { assignVars = mp1
                                           , assignTrace = ls : lss
                                           , ..
                                           } )
        _ -> panic "Unbound variable in assignment trace."
    _ -> panic "Tried to undo a non-existent assignment."



-- | Undo the assignments in the top-most decision level.
-- PRE: We are not at level 0.
assignCancel :: Assignment -> Assignment
assignCancel Assignment { .. } =
  case assignTrace of
    ls : more -> Assignment
                  { assignVars = foldr Map.delete assignVars (map litVar ls)
                  , assignTrace = more
                  , assignDecisionLevel = assignDecisionLevel - 1
                  }
    [] -> panic "Tried to `assignCancel` at the top-level."

-- | Cancel assignments until we are at the specified decsion level.
assignCancelTill :: Int -> Assignment -> Assignment
assignCancelTill lvl a
  | assignDecisionLevel a > lvl = assignCancelTill lvl (assignCancel a)
  | otherwise                   = a

--------------------------------------------------------------------------------
-- Watch Lists
--------------------------------------------------------------------------------

type ClauseId      = Int

-- | A clause on a watch list.  These clauses have a unique id, that we can
-- use to identify them.
data WatchedClause = WCla { watchedId     :: ClauseId
                          , watchedClause :: Clause
                          }

data Watchers = Watchers
  { watchExamine      :: Map Literal [WatchedClause]
    -- ^ Which clauses to examine when a literal becomes true.

  , watched           :: Map ClauseId (Literal,Literal)
    -- ^ Which literals are being watched in a clause.

  , watchNextClauseId :: !Int
    -- ^ Local clause ids, used to keep track of the watched literals.
  }

-- | Introduce a new clause to the watcher system.
-- The two literals should be distinct and appear negated in the clause.
watchNewClause :: Literal -> Literal -> Clause -> Watchers -> Watchers
watchNewClause l1 l2 cla Watchers { .. } =
  Watchers { watchExamine       = Map.insertWith (++) l1 [wcla]
                                $ Map.insertWith (++) l2 [wcla]
                                 watchExamine
           , watched           = Map.insert watchNextClauseId (l1,l2) watched
           , watchNextClauseId = 1 + watchNextClauseId
           }
  where wcla = WCla { watchedId     = watchNextClauseId
                    , watchedClause = cla
                    }

-- | Remove the clauses interested in the given literal being true.
-- The clauses should be re-inserted using either
-- 'watchMoveClause', or 'watchReinsert'
-- For each clause we also return the other watched lietral.
watchGetClauses :: Literal -> Watchers -> ([(WatchedClause, Literal)], Watchers)
watchGetClauses l Watchers { .. } =
  case Map.updateLookupWithKey (\_ _ -> Nothing) l watchExamine of
    (Nothing,_)     -> ([], Watchers { .. })
    (Just clas, n1) -> ([ (c, otherLit c) | c <- clas ]
                       , Watchers { watchExamine = n1, .. })
  where
  otherLit WCla { .. } =
    case Map.lookup watchedId watched of
      Nothing      -> panic "Missing watched pair."
      Just (l1,l2) -> if l == l1 then l2 else l1


-- | Add a clause to a new watch list.  Assumes that the clause has
-- been removed from its old list.  The first literal is the new location
-- the second one is the other (unchanged) location.
watchMoveClause :: Literal -> (WatchedClause, Literal) -> Watchers -> Watchers
watchMoveClause newLoc (cla,otherLoc)  Watchers { .. } =
  Watchers { watchExamine = Map.insertWith (++) newLoc [cla] watchExamine
           , watched      = Map.insert (watchedId cla) (newLoc,otherLoc) watched
           , ..
           }

-- | Insert back previously extracted clauses.
-- Note that when we extract the clauses, we don't remove them from
-- the 'watched' map, so we just need to re-insert the clauses in the
-- 'watchExamine' map.
watchReinsert :: Literal -> [(WatchedClause, Literal)] -> Watchers -> Watchers
watchReinsert l cs Watchers { .. } =
  Watchers { watchExamine = Map.insertWith (++) l (map fst cs) watchExamine
           , ..
           }


--------------------------------------------------------------------------------
-- Solver's State
--------------------------------------------------------------------------------

data S = S
  { sAssignment     :: Assignment
    -- ^ Bindings for variables, with provinance.

  , sWatching       :: Watchers
    -- ^ For each literal, we remember whom to notify when it becomes true.

  }


--------------------------------------------------------------------------------
-- Propagation
--------------------------------------------------------------------------------


-- | Propagating information that the given literals became true.
solPropagate :: Seq Literal -> S -> (Maybe Clause, S)
solPropagate q s =
  case Seq.viewl q of
    Seq.EmptyL -> (Nothing, s)
    l :< more ->
      case solPropagate1 l s of
        (Right newWork, s1) -> solPropagate (more >< newWork) s1
        (Left cla,      s1) -> (Just cla, s1)


{- | Propagate the information that the given literal became true.
Returns a conflict clause, if one is found.
This function uses the watch list to propagate the information.

INV: While working, clauses are temporarily removed from their watched lists,
but by the time we return, all clauses should be back on some watch list. -}
solPropagate1 :: Literal -> S -> (Either Clause (Seq Literal), S)
solPropagate1 l s0 = go Seq.empty s0 { sWatching = ws1 } clas
  where
  (clas, ws1) = watchGetClauses l (sWatching s0)

  go q s [] = (Right q, s)
  go q s (cla : more) =
    case solExamineClause l cla s of
      (Done,s1)     -> go q s1 more
      (NewWork,s1)  -> go (q |> snd cla) s1 more   -- enque other literal
      (Conflict,s1) ->
         ( Left (watchedClause (fst cla))
         , s1 { sWatching = watchReinsert l more (sWatching s1) }
         )


data ExamResult = Conflict | NewWork | Done

{- | Examine the clause, in light of the literal becoming true.
The clause should re-inesert itself in the watchers datastructure.
The boolean indicates if we found a conflict. -}
solExamineClause :: Literal -> (WatchedClause, Literal) -> S -> (ExamResult, S)
solExamineClause l it@(cla, otherLit) S { .. } =

  case assignGetLit otherLit sAssignment of

    -- The other literal is already true, we just put oursleves back in place.
    Just True -> ( Done
                 , S { sWatching = watchReinsert l [it] sWatching
                     , .. })

    -- Try to find another unbound literal.
    _ -> case claFindLit newUnbound (watchedClause cla) of
           Just newL -> ( Done
                        , S { sWatching = watchMoveClause newL it sWatching
                            , .. } )

           -- A unit clause.
           Nothing ->
             let s = S { sWatching = watchReinsert l [it] sWatching, .. }
             in case solSetTrue otherLit (Just (watchedClause cla)) s of
                  Just (newWork, s1) -> (if newWork then NewWork else Done, s1)
                  Nothing            -> ( Conflict,                          s )
  where
  x1           = litVar otherLit
  x2           = litVar l
  newUnbound x = x /= x1 && x2 /= x2 && not (assignDefines x sAssignment)


{- | Set a literal to true in the given state.
Fails, if doing so results in a conflict.
On sucess, we return a boolean flag, indicating if more work needs to
be propagated, and the new state. -}
solSetTrue :: Literal -> Maybe Clause -> S -> Maybe (Bool, S)
solSetTrue l impliedBy S { .. } =
  case assignGetLit l sAssignment of
    Just True  -> Just (False, S { .. }) -- Already known to be true
    Just False -> Nothing                -- Already known to be false
    Nothing -> Just (True, S { sAssignment = newA, .. })
      where newA = assignSetLit l impliedBy sAssignment



--------------------------------------------------------------------------------
-- Backtracking
--------------------------------------------------------------------------------



-- | The state used while analyzigin a conflict clause.
data AnaS = AnaS { asAssign :: !Assignment
                   -- ^ Assignment, slowly being backtracked.

                 , asSeen   :: !(Set Variable)
                   -- ^ Set of processed variables.

                 , asUndo   :: !Int
                   -- ^ How many literals at the current level need undoing.

                 , asLearn  :: [Literal]
                   -- ^ Learned clause

                 , asMaxLvl :: !Int
                   -- ^ Maximum decision level for literals in learned clause.

                 , asMaxLvlLit :: Maybe Literal
                   -- ^ Literal with maximum decision level.
                   -- This is used as the second literal to watch in
                   -- the learnt clause.
                 }


{- | Analyze a conflict clause and back-track.
Returns a ( new learned clause
          , a literal in the clause to watch
          , a second literal in the clause to waty (if any)
          , new backtracked assignemnt
          )

Assumes that we are not at decision level 0.
-}

analyzeConflict :: Clause -> S -> (Clause, Literal, Maybe Literal, Assignment)
analyzeConflict confl S { .. } = checkReason s0 (claReason confl)

  where
  s0 = AnaS { asAssign    = sAssignment
            , asSeen      = Set.empty
            , asUndo      = 0
            , asLearn     = []
            , asMaxLvl    = 0
            , asMaxLvlLit = Nothing
            }

  checkReason s [] = undoRelevantOne s

  checkReason AnaS { .. } (l : ls) =
                            checkReason s1 { asSeen = Set.insert x asSeen } ls
    where
    x        = litVar l
    Just lvl = assignGetLevel x asAssign

    s1 -- We've already processed this literal: do nothing.
      | x `Set.member` asSeen = AnaS { .. }

      -- A literal at the current decision level: increment the number of
      -- literals that need undoing.
      | lvl == assignDecisionLevel asAssign = AnaS { asUndo = 1 + asUndo, .. }

      -- A literal that was assigned as a guess at a previous level:
      -- add to the learned clause, and update the max. decision level.
      | lvl > 0 = if lvl > asMaxLvl
                     then AnaS { asLearn     = l : asLearn
                               , asMaxLvl    = lvl
                               , asMaxLvlLit = Just l
                               , .. }
                     else AnaS { asLearn = l : asLearn, .. }

      -- A literal that was assigned at level 0: can't expand any further.
      | otherwise = AnaS { .. }


  undoRelevantOne AnaS { .. } =
    case assignUndoLast asAssign of
      (l, ai, agn1)

        -- Some other irrelevant variable?
        | not (litVar l `Set.member` asSeen) ->
          undoRelevantOne AnaS { asAssign = agn1, .. }

        -- Is this the last one?
        | asUndo == 1 ->
          let newL = litNeg l
          in case claFromList (litNeg l : asLearn) of
               Just cla -> ( cla
                           , newL, asMaxLvlLit
                           , assignCancelTill asMaxLvl asAssign
                           )
               Nothing  -> panic "Trivial learned clause?"

        -- Let's investigate the reason for the assignment.
        | otherwise ->
          case assignImpliedBy ai of
            Nothing  -> panic "Undoing a non-implied assignment."
            Just cla -> checkReason
                          AnaS { asAssign = agn1
                               , asUndo   = asUndo -1
                               , .. }
                          (claReasonFor l cla)

--------------------------------------------------------------------------------
-- Misc
--------------------------------------------------------------------------------

panic :: String -> a
panic msg = error ("[BUG] " ++ msg)


