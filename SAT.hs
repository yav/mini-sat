module SAT where

import Data.Map(Map)
import qualified Data.Map as Map
import qualified Data.IntMap as IntMap
import qualified Data.Set as Set
import qualified Data.IntSet as IntSet
import qualified Data.List as List
import Data.Maybe(mapMaybe)
import Data.Foldable(toList)
import Control.Monad(foldM)

import qualified Ersatz.Solution as Ersatz
import qualified Ersatz.Problem as Ersatz
import qualified Ersatz.Internal.Formula as Ersatz
import qualified Ersatz.Solver.Minisat as Ersatz

import Debug.Trace


solver :: Ersatz.Solver Ersatz.SAT IO
solver (Ersatz.SAT n f _) =
  do print n
     case check (mapMaybe toCl (toList (Ersatz.formulaSet f))) of
       Nothing -> return (Ersatz.Unsatisfied, IntMap.empty)
       Just xs -> do print xs
                     return ( Ersatz.Satisfied, IntMap.fromList (Map.toList xs))
  where
  toCl :: Ersatz.Clause -> Maybe Clause
  toCl cl = traverse one $ Map.fromListWith (++)
              [ (abs x, [if x > 0 then Pos else Neg])
                      | x <- IntSet.toList (Ersatz.clauseSet cl) ]

  one [x] = return x
  one _   = Nothing

type Var      = Int
data Polarity = Neg | Pos deriving (Eq,Ord,Show)
data Lit      = Lit { litPolarity :: Polarity, litVar :: Var }
                  deriving Show

type Assignment = Map Var Bool

polarity :: Polarity -> Bool -> Bool
polarity p = case p of
               Pos -> id
               Neg -> not

-- | The value of a varible in the given assignment, if any.
lookupVar :: Var -> Assignment -> Maybe Bool
lookupVar = Map.lookup

type Clause = Map Var Polarity

-- | Nothing means that not all variables were defined.
evalClause :: Assignment -> Clause -> Maybe Bool
evalClause agn cs = or <$> mapM ev (Map.toList cs)
  where ev (x,p) = polarity p <$> lookupVar x agn


polarityOf :: Var -> Clause -> Polarity
polarityOf x c = c Map.! x


data Clause1  = Clause1 Var     Clause deriving Show
data Clause2  = Clause2 Var Var Clause deriving Show
type ClauseId = Int

data State = State
  { assigned    :: Assignment
  , unassigned  :: [Var]
  , monitored   :: Map Var [ClauseId]
  , incomplete  :: Map ClauseId Clause2
  , guesses     :: [(Var,State)]
  } deriving Show


check :: [Clause] -> Maybe Assignment
check cs =
  do (vs, c1,c2) <- foldM preProc (Set.empty, [],[]) cs
     let inc = zip [ 0 .. ] c2 :: [(Int,Clause2)]
         s   = State { assigned   = Map.empty
                     , unassigned = 7 : 2 : [ x | x <- Set.toList vs, x /= 2 && x /= 7 ]
                     , monitored  = Map.fromListWith (++)
                                      [ v | (i, Clause2 x y _) <- inc
                                          , v <- [ (x,[i]), (y,[i]) ]
                                      ]
                     , incomplete = Map.fromList inc
                     , guesses    = []
                     }
     sln <- checkSat c1 s
     case mapM (evalClause sln) cs of
       Just xs | and xs -> return ()
               | otherwise ->
                error $ unlines ("Not all clauses were true:"
                                  : map show (zip xs cs))

       Nothing -> error "Not all variables were assigned"

     return sln


  where
  preProc (vs,c1,c2) c =
    do let vs1 = Set.union (Map.keysSet c) vs
       ((x,_),rest) <- Map.minViewWithKey c
       case Map.minViewWithKey rest of
         Nothing    -> return (vs1, Clause1 x c : c1, c2)
         Just ((y,_),_) -> return (vs1, c1, Clause2 x y c : c2)


checkSat :: [Clause1] -> State -> Maybe Assignment
checkSat sing s =
  case sing of
    []  -> guess s
    Clause1 x c : more ->
      case lookupVar x (assigned s) of
        Just b
          | polarity p b -> checkSat more s
          | otherwise    -> backtrack s
        Nothing -> let v = polarity p True
                   in setVar more x v s
      where
      p = polarityOf x c


backtrack :: State -> Maybe Assignment
backtrack s =
  case guesses s of
    [] -> Nothing
    (x,s1) : _ -> checkSat [Clause1 x learn] s1
  where
  learn = Map.fromList [ (x,Neg) | (x,_) <- guesses s ]



guess :: State -> Maybe Assignment
guess s =
  case unassigned s of
    x : _ -> setVar [] x True s { guesses = (x,s) : guesses s }
    []    -> return (assigned s)


setVar :: [Clause1] -> Var -> Bool -> State -> Maybe Assignment
setVar sing v b s0 =
  let s = s0 { assigned   = Map.insert v b (assigned s0)
             , unassigned = List.delete v (unassigned s0)
             }
  in
  case Map.lookup v (monitored s) of
    Nothing -> checkSat sing s
    Just xs ->
      case updClauses v b s xs of
        (sings,s1) -> checkSat (sings ++ sing) s1   -- does order matter?

data SetVar2Result = Complete | Watched Clause2 | Singleton Clause1

updClauses :: Var -> Bool -> State -> [ClauseId] -> ([Clause1],State)
updClauses x v s0 = List.foldl' upd ([],s0)
  where
  agn = assigned s0

  upd done@(sing,s) cid =
    case Map.lookup cid (incomplete s) of
      Nothing -> done
      Just wa ->
        case setVarInClause2 agn x v wa of
          Complete    -> done
          Watched w@(Clause2 n _ _)   ->
              (sing, s { incomplete = Map.insert cid w (incomplete s)
                       , monitored  = Map.insertWith (++) n [cid] (monitored s)
                        })
          Singleton c@(Clause1 x _) -> (c : sing, s)


setVarInClause2 :: Assignment -> Var -> Bool -> Clause2 -> SetVar2Result
setVarInClause2 agn x v (Clause2 a b c) =
  let r = foldr pick (Singleton (Clause1 other c)) (Map.toList c)
  in case r of
       Singleton (Clause1 _ c)
          | all check (Map.toList c) -> r
          | otherwise -> error "Not singleton"
       _ -> r
  where
  check (v1,p) = case lookupVar v1 agn of
                   Nothing -> v1 == other
                   Just b -> polarity p b == False

  (this,other) = if x == a then (a,b) else (b,a)

  pick (v1,p1) notMe
    | Just y <- lookupVar v1 agn = if polarity p1 y then Complete else notMe
    | v1 == this  = notMe
    | v1 == other = notMe
    | otherwise = Watched (Clause2 v1 other c)  -- new var is first


