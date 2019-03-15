module ErSAT (solver) where

import Data.Maybe(mapMaybe)
import Data.Foldable(toList)

import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import qualified Ersatz.Solution as Ersatz
import qualified Ersatz.Problem as Ersatz
import qualified Ersatz.Internal.Formula as Ersatz

import SAT

solver :: Ersatz.Solver Ersatz.SAT IO
solver (Ersatz.SAT n f _) =
  do putStrLn ("Variables: " ++ show n)
     let cs = mapMaybe toCl (toList (Ersatz.formulaSet f))
     putStrLn ("Clauses: " ++ show (length cs))
     case check cs of
       Nothing -> return (Ersatz.Unsatisfied, IntMap.empty)
       Just xs -> return (Ersatz.Satisfied, xs)
  where
  toCl :: Ersatz.Clause -> Maybe (IntMap Polarity)
  toCl cl = let c  = Ersatz.clauseSet cl
                vs = abs `IntSet.map` c
            in if IntSet.size vs == IntSet.size c
                  then Just (toMp c)
                  else Nothing

  toMp :: IntSet -> IntMap Polarity
  toMp = IntMap.fromList . map toEntry . IntSet.toList

  toEntry :: Int -> (Int,Polarity)
  toEntry x = (abs x, if x > 0 then Positive else Negated)

