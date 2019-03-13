module ErSAT (solver) where

import Data.Map(Map)
import qualified Data.Map as Map
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
       Just xs -> return (Ersatz.Satisfied, toSln xs)
  where
  toCl :: Ersatz.Clause -> Maybe (Map Var Polarity)
  toCl cl = let c  = Ersatz.clauseSet cl
                vs = abs `IntSet.map` c
            in if IntSet.size vs == IntSet.size c
                  then Just (toMp c)
                  else Nothing

  toMp :: IntSet -> Map Var Polarity
  toMp = Map.fromList . map toEntry . IntSet.toList

  toEntry :: Int -> (Var,Polarity)
  toEntry x = (Var (abs x), if x > 0 then Positive else Negated)

  toSln :: Assignment -> IntMap Bool
  toSln agn = IntMap.fromList [ (x,b) | (Var x,b) <- Map.toList agn ]


