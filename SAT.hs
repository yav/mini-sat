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
data Polarity = Neg | Pos deriving (Eq,Ord,Show)
data Lit      = Lit { litPolarity :: Polarity, litVar :: Var }
                  deriving Show

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

polarity :: Polarity -> Bool -> Bool
polarity p = case p of
               Pos -> id
               Neg -> not

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


polarityOf :: Var -> Clause -> Polarity
polarityOf x c = if IntSet.member x c then Pos else Neg


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
     sln <- checkSat c1 s
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

importClause :: Clause -> Maybe (Either Clause1 Clause2)
importClause c =
  do (x,rest) <- IntSet.minView c
     case IntSet.minView rest of
       Nothing    -> return $ Left (Clause1 (abs x) c)
       Just (y,_) -> return $ Right (Clause2 (abs x) (abs y) c)




checkSat :: [Clause1] -> State -> Maybe Assignment
checkSat sing s =
  case sing of
    []  -> guess s
    Clause1 x c : more ->
      case lookupVar x agn of
        Just b
          | polarity p b -> checkSat more s
          | otherwise    -> backtrack s c
        Nothing ->
          setVar more reason x val s
      where
      agn     = assigned s
      p       = polarityOf x c
      val     = polarity p True
      reason  = IntSet.unions
                    [ lookupReason v agn | v' <- IntSet.toList c
                                         , let v = abs v', v /= x ]

backtrack :: State -> Clause -> Maybe Assignment
backtrack s c =
  case dropWhile notRelevant (guesses s) of
    [] -> Nothing
    (x,s1) : more ->
      let (nonrs,rs) = span notRelevant more
          c1 = Clause1 x learn
          st = case map snd nonrs of
                 [] -> s { assigned = s1, guesses = more }
                 ss -> s { assigned = last ss, guesses = rs }
      in case map fst rs of
           [] -> checkSat [c1] st
           y : _ -> let w2 = Clause2 x y learn
                    in checkSat [c1] (newClause2 w2 st)
  where
  reasons = IntSet.unions $ map ((`lookupReason` assigned s) . abs)
                          $ IntSet.toList c
  learn   = IntSet.fromList [ negate v | v <- IntSet.toList reasons ]
  notRelevant (x,_) = not (x        `IntSet.member` learn ||
                           negate x `IntSet.member` learn)




guess :: State -> Maybe Assignment
guess s =
  case todo (assigned s) of
    x : _ -> setVar [] (IntSet.singleton x)
                       x True s { guesses = (x, assigned s) : guesses s }
    []    -> return (assigned s)


setVar :: [Clause1] -> Reason -> Var -> Bool -> State -> Maybe Assignment
setVar sing reason v b s0 =
  let s = s0 { assigned = addVarDef v (b,reason) (assigned s0) }
  in
  case IntMap.lookup v (monitored s) of
    Nothing -> checkSat sing s
    Just xs ->
      case updClauses v b s xs of
        Left c -> backtrack s c
        Right (sings,s1) -> checkSat (sings ++ sing) s1   -- does order matter?

data SetVar2Result = Complete | Watched Clause2 | Singleton Clause1

updClauses ::
  Var -> Bool -> State -> [ClauseId] -> Either Clause ([Clause1],State)
updClauses x v s0 = foldM upd ([],s0)
  where
  agn = assigned s0

  upd done@(sing,s) cid =
    case IntMap.lookup cid (incomplete s) of
      Nothing -> Right done
      Just wa ->
        case setVarInClause2 agn x v wa of
          Complete    -> Right done
          Watched w@(Clause2 n _ _)   ->
              Right ( sing
                   , s { incomplete = IntMap.insert cid w (incomplete s)
                       , monitored  = IntMap.insertWith (++) n [cid]
                                    $ IntMap.adjust (List.delete cid) x
                                    $ monitored s
                   })
          Singleton si@(Clause1 y c)
            | Just b <- lookupVar y agn ->
              if polarity (polarityOf y c) b then Right done else Left c
            | otherwise -> Right (si:sing,s)


setVarInClause2 :: Assignment -> Var -> Bool -> Clause2 -> SetVar2Result
setVarInClause2 agn x v (Clause2 a b c)
  | polarity (polarityOf x c) v = Complete
  | otherwise = foldr pick (Singleton (Clause1 other c)) (IntSet.toList c)
  where
  other = if x == a then b else a

  pick l notMe
    | v1 == x || v1 == other     = notMe
    | Just y <- lookupVar v1 agn = if polarity p1 y then Complete else notMe
    | otherwise                  = Watched (Clause2 v1 other c)
                                   -- new var is first
      where v1 = abs l
            p1 = if l > 0 then Pos else Neg


