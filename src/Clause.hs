{-# LANGUAGE Safe #-}
{-# LANGUAGE BangPatterns #-}

-- | Implementation of clauses.
module Clause
  ( Clause
  , claFromList
  , claIsFalse
  , claFindLit
  , claReasonFor
  , claReason
  ) where

import           Var ( Variable, Literal, litVar, litNeg )

import qualified Data.Set as Set
import qualified Data.Array.Unboxed as Arr
import           Data.Array.Unboxed ( UArray, listArray, rangeSize )
import           Data.Maybe ( listToMaybe )



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



