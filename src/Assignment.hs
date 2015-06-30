{-# LANGUAGE Safe #-}
{-# LANGUAGE RecordWildCards #-}
-- | Implementation of Assignments.
module Assignment
  ( Assignment
  , assignDecisionLevel
  , assignDefines
  , assignGetLit
  , assignGetLevel
  , assignSetLit
  , assignUndoLast
  , assignCancel
  , assignCancelTill

  , AssignInfo
  , assignImpliedBy
  ) where

import Var
import Clause
import Utils

import qualified Data.Map as Map
import           Data.Map ( Map )


-- | An assignment keeps track of the current values for variables.
-- In addition, it keeps track of how these assignments came to be.
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

