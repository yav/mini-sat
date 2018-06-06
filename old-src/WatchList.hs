{-# LANGUAGE Safe #-}
{-# LANGUAGE RecordWildCards #-}

{- | Implementation of watch lists.
These are used to keep track of false literals in clauses, which helps
with efficient propagation of information.  The basic idea is that a
we don't need to do anything with clasues that have at least two unassigned
literals, however as long as there is only one unassigned literal left,
then we need to propagate the fact that this literal is true.
-}
module WatchList
  ( Watchers
  , WatchedClause
  , watchNewClause
  , watchedClause
  , watchGetClauses
  , watchReinsert
  , watchMove
  ) where

import Var
import Clause
import Utils

import qualified Data.Map as Map
import           Data.Map ( Map )

-- | The main data strucutre keeping track of the various watch lists.
data Watchers = Watchers
  { watchExamine      :: Map Literal [WatchedClause]
    -- ^ Which clauses to examine when a literal becomes true.

  , watched           :: Map ClauseId (Literal,Literal)
    -- ^ Which literals are being watched in a clause.

  , watchNextClauseId :: !Int
    -- ^ Local clause ids, used to keep track of the watched literals.
  }


type ClauseId      = Int

-- | A clause on a watch list.  These clauses have a unique id, that we can
-- use to identify them.
data WatchedClause = WCla { watchedId     :: ClauseId
                          , watchedClause :: Clause
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
watchMove :: Literal -> (WatchedClause, Literal) -> Watchers -> Watchers
watchMove newLoc (cla,otherLoc)  Watchers { .. } =
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

