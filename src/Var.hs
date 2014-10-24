{-# LANGUAGE Trustworthy #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}  -- For unboxed arrays of literals

-- | Variables and Literals
module Var
  ( -- * Variables
    Variable, var

    -- * Literals
  , Literal, lit, litNeg, litVar, litIsPos
  ) where

import           Data.Array.Unboxed ( IArray, UArray )

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


