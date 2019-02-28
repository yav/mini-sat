module SAT where

import           Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import           Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import qualified Data.List as List
import Data.Maybe(mapMaybe)
import Data.Foldable(toList)
import Control.Monad(foldM)

import qualified Ersatz.Solution as Ersatz
import qualified Ersatz.Problem as Ersatz
import qualified Ersatz.Internal.Formula as Ersatz



solver :: Ersatz.Solver Ersatz.SAT IO
solver (Ersatz.SAT n f _) =
  do putStrLn ("Variables: " ++ show n)
     case check (mapMaybe toCl (toList (Ersatz.formulaSet f))) of
       Nothing -> return (Ersatz.Unsatisfied, IntMap.empty)
       Just xs -> return ( Ersatz.Satisfied
                         , IntMap.fromList (IntMap.toList (fst <$> varVals xs))
                         )
  where
  toCl :: Ersatz.Clause -> Maybe Clause
  toCl cl = let c  = Ersatz.clauseSet cl
                vs = abs `IntSet.map` c
            in if IntSet.size vs == IntSet.size c then Just c else Nothing

type Var      = Int

data Assignment = Assignment
  { varVals :: IntMap {-Var-} (Bool, Reason)
  , todo    :: [Var]
  } deriving Show

addVarDef :: Var -> (Bool, Reason) -> Assignment -> Assignment
addVarDef v b a = Assignment
  { varVals = IntMap.insert v b (varVals a)
  , todo    = List.delete v (todo a)
  }


type Reason     = IntSet {-Guess-}


-- | The value of a varible in the given assignment, if any.
lookupVar :: Var -> Assignment -> Maybe Bool
lookupVar v a = fst <$> IntMap.lookup v (varVals a)

lookupReason :: Var -> Assignment -> Reason
lookupReason v a =
  case IntMap.lookup v (varVals a) of
    Just (_,r) -> r
    Nothing    -> error ("Variable " ++ show v ++ " is not assigned")

type Clause = IntSet {-Lit-}

-- | Nothing means that not all variables were defined.
evalClause :: Assignment -> Clause -> Maybe Bool
evalClause agn cs = or <$> mapM ev (IntSet.toList cs)
  where ev l = let v = lookupVar (abs l) agn
               in if l > 0 then v else not <$> v

polarityOf :: Var -> Clause -> Bool -> Bool
polarityOf x c = if x `IntSet.member` c then id else not




data Clause1  = Clause1 Var     Clause deriving Show
data Clause2  = Clause2 Var Var Clause deriving Show
type ClauseId = Int

data State = State
  { assigned    :: Assignment
  , monitored   :: IntMap {-Var-} [ClauseId]
  , nextCid     :: Int
  , incomplete  :: IntMap {-ClauseId-} Clause2
  , guesses     :: [(Var,Assignment)]
  } deriving Show

-- | Add a new clause with at least 2 unasigned variables to the system.
newClause2 :: Clause2 -> State -> State
newClause2 w@(Clause2 x y _) s =
  s { incomplete = IntMap.insertWith (error "bug") cid w (incomplete s)
    , monitored  = IntMap.insertWith (++) x [cid]
                 $ IntMap.insertWith (++) y [cid]
                 $ monitored s
    , nextCid = cid + 1
    }

  where
  cid = nextCid s

check :: [Clause] -> Maybe Assignment
check cs =
  do (vs, c1,c2) <- foldM preProc (IntSet.empty, [],[]) cs
     let inc = zip [ 0 .. ] c2 :: [(Int,Clause2)]
         s   = State { assigned   = Assignment { varVals = IntMap.empty
                                               , todo    = IntSet.toList vs
                                               }
                     , monitored  = IntMap.fromListWith (++)
                                      [ v | (i, Clause2 x y _) <- inc
                                          , v <- [ (x,[i]), (y,[i]) ]
                                      ]
                     , nextCid    = length inc
                     , incomplete = IntMap.fromList inc
                     , guesses    = []
                     }
     sln <- continue $ foldM (flip setVarFromClause1) s c1
     case mapM (evalClause sln) cs of
       Just xs | and xs -> return ()
               | otherwise ->
                error $ unlines ("Not all clauses were true:"
                                  : map show (zip xs cs))

       Nothing -> error "Not all variables were assigned"

     return sln


  where
  preProc (vs,c1s,c2s) c =
    do let vs1 = IntSet.union (abs `IntSet.map` c) vs
       ty <- importClause c
       case ty of
         Left c1 -> return (vs1, c1 : c1s, c2s)
         Right c2 -> return (vs1, c1s, c2 : c2s)

-- | Classify a clause: 'Nothing' means that the clause was empty,
-- and thus trivially false.
importClause :: Clause -> Maybe (Either Clause1 Clause2)
importClause c =
  do (x,rest) <- IntSet.minView c
     case IntSet.minView rest of
       Nothing    -> return $ Left (Clause1 (abs x) c)
       Just (y,_) -> return $ Right (Clause2 (abs x) (abs y) c)


-- | We do this once we've finished propagating some information.
continue :: Either Conflict State -> Maybe Assignment
continue what =
  case what of
    Left c  -> backtrack c
    Right s -> guess s

-- | Set the value of a variable, and propagate the effects.
setVar :: Var -> Bool -> Reason -> State -> Either Conflict State
setVar x b reason s =
  propagate x b s { assigned = addVarDef x (b,reason) (assigned s) }


-- | Try to set the value of a variable, using a singleton clause.
-- Fails if the variables has already been assigned in a conflicting way.
setVarFromClause1 :: Clause1 -> State -> Either Conflict State
setVarFromClause1 (Clause1 x c) s =
  case lookupVar x agn of
    Just b1 -> if b1 == val then return s else Left (Conflict c s)
    Nothing -> setVar x val reason s
  where
  agn     = assigned s
  val     = polarityOf x c True
  reason  = IntSet.unions [ lookupReason v agn
                          | v' <- IntSet.toList c
                          , let v = abs v'
                          , v /= x ]

-- | Try to set a variable by just guessing a value for it.
guess :: State -> Maybe Assignment
guess s =
  case todo (assigned s) of
    x : _ ->
      let reason = IntSet.singleton x
          s1 = s { guesses  = (x, assigned s) : guesses s
                 , assigned = addVarDef x (True,reason) (assigned s) }
      in continue $ propagate x True s1
    []    -> return (assigned s)




data Conflict = Conflict Clause State

-- | Resolve the given conflict by backtracking.
backtrack :: Conflict -> Maybe Assignment
backtrack (Conflict c s) =
  case dropWhile notRelevant (guesses s) of
    [] -> Nothing
    (x,s1) : more ->
      let (nonrs,rs) = span notRelevant more
          c1 = Clause1 x learn
          st = case map snd nonrs of
                 [] -> s { assigned = s1, guesses = more }
                 ss -> s { assigned = last ss, guesses = rs }
      in continue
       $ setVarFromClause1 c1
       $ case map fst rs of
           []    -> st
           y : _ -> newClause2 (Clause2 x y learn) st
  where
  reasons = IntSet.unions $ map ((`lookupReason` assigned s) . abs)
                          $ IntSet.toList c
  learn   = IntSet.fromList [ negate v | v <- IntSet.toList reasons ]
  notRelevant (x,_) = not (x        `IntSet.member` learn ||
                           negate x `IntSet.member` learn)


-- | Propagate the fact that a variable got a speicific value.
propagate :: Var -> Bool -> State -> Either Conflict State
propagate x b s0 =
  case IntMap.lookup x (monitored s0) of
    Nothing  -> Right s0
    Just cs2 -> foldM prop s0 cs2
  where
  prop s cid =
    case IntMap.lookup cid (incomplete s) of
      Nothing -> Right s
      Just wa ->
        case setVarInClause2 (assigned s) x b wa of
          Complete -> Right s
          Watched w@(Clause2 n _ _) ->
            Right s { incomplete = IntMap.insert cid w (incomplete s)
                    , monitored  = IntMap.insertWith (++) n [cid]
                                 $ IntMap.adjust (List.delete cid) x
                                 $ monitored s
                    }
          Singleton si -> setVarFromClause1 si s


data SetVar2Result = Complete           -- ^ Clause was already satisifed
                   | Watched Clause2    -- ^ The new watched clause
                   | Singleton Clause1  -- ^ The clause became a singleton

-- | Update a watched clause, after a variable is assigned.
setVarInClause2 :: Assignment -> Var -> Bool -> Clause2 -> SetVar2Result
setVarInClause2 agn x v (Clause2 a b c)
  | polarityOf x c v = Complete
  | otherwise = foldr pick (Singleton (Clause1 other c)) (IntSet.toList c)
  where
  other = if x == a then b else a

  pick l notMe
    | v1 == x || v1 == other     = notMe
    | Just y <- lookupVar v1 agn = if p1 y then Complete else notMe
    | otherwise                  = Watched (Clause2 v1 other c)
                                   -- new var is first
      where v1 = abs l
            p1 = if l > 0 then id else not


