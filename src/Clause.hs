{-# LANGUAGE Safe #-}
{-# LANGUAGE BangPatterns #-}

-- | Implementation of clauses.
module Clause
  ( Clause
  , claFalse
  , claFromList
  , claIsFalse
  , claFindLit
  , claReasonFor
  , claReason
  ) where

import           Var ( Variable, Literal(..), litVar, litNeg )

import qualified Data.IntSet as IntSet
import qualified Data.Array.Unboxed as Arr
import           Data.Array.Unboxed ( UArray, listArray, rangeSize )
import           Data.Maybe ( listToMaybe )



-- | A "list" of literals.
newtype Clause  = Cla (UArray Int Int{-Literal-})


claFalse :: Clause
claFalse = Cla (listArray (0,-1) [])

-- | Create a clause from the list of literals.
-- Returns 'Nothing' if the clause is trivially true.
claFromList :: [Literal] -> Maybe Clause
claFromList = go 0 IntSet.empty
  where
  go !len seen [] = Just $ Cla $ listArray (0,len-1) $ IntSet.toList seen
  go !len seen (l@(Lit x) : xs)
    | x  `IntSet.member` seen  = go len seen xs
    | nx `IntSet.member` seen  = Nothing
    | otherwise                = go (len + 1) (IntSet.insert x seen) xs
    where Lit nx = litNeg l

-- | Is this a false (i.e., empty) clause.
claIsFalse :: Clause -> Bool
claIsFalse (Cla mp) = rangeSize (Arr.bounds mp) == 0

-- | Fine a literal, whose variable satisfies the condition.
claFindLit :: (Variable -> Bool) -> Clause -> Maybe Literal
claFindLit isOk (Cla mp) =
  listToMaybe [ l | x <- Arr.elems mp, let l = Lit x, isOk (litVar l) ]

-- | If the clause is the reason for the literal to become true,
-- then all other literals must have been false.
claReasonFor :: Literal -> Clause -> [Literal]
claReasonFor l (Cla mp) =
  [ litNeg l1 | x <- Arr.elems mp, let l1 = Lit x, l1 /= l ]

-- | If the clause became false, then all its literals must be false.
claReason :: Clause -> [Literal]
claReason (Cla mp) = [ litNeg (Lit l) | l <- Arr.elems mp ]



