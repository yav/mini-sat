{-# LANGUAGE Safe #-}
{-# LANGUAGE RecordWildCards #-}

module SAT where

import           Var
import           Clause
import           Assignment
import           WatchList
import           Utils

import           Data.Set ( Set )
import qualified Data.Set as Set
import           Data.Sequence (Seq, ViewL(..), (|>), (><))
import qualified Data.Sequence as Seq



-- | Solver's State
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
                        , S { sWatching = watchMove newL it sWatching
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


