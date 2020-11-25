module Interaction where

import TermData
import TermFunctions
import InferenceRules
import SpecialMatches
import Util
import Printing
import Quoting

import Control.Unification
import Control.Monad
import Control.Monad.Trans.Except
import Control.Monad.Trans
import Debug.Trace
import Data.List

type Conj a = [a]
type Disj a = [a]

type PossMap a b = [(a,[b])]
type GoalToPossMap m = PossMap (KB,OpenTerm) (Clause, IntBindMonQuanT m Clause)
type IdxGoalToPossMap m = PossMap (KB,OpenTerm) (Int, (Clause, IntBindMonQuanT m Clause))
type GoalToNextStateMap m = PossMap (KB,OpenTerm) (IntBindMonQuanT m [(KB,OpenTerm)])
type IdxGoalToNextStateMap m = PossMap (KB,OpenTerm) (Int, IntBindMonQuanT m [(KB,OpenTerm)])

interactiveProof :: RawKB -> [(RawKB,OpenTerm)] -> IntBindMonQuanT IO ()
interactiveProof solvekb goals = do {
  goals' <- sequence $ [readRawKB kb >>= \kb' -> return (kb', gs) |(kb,gs) <- goals];
  solvekb' <- readRawKB solvekb;
  interactiveProofPreread solvekb' goals'
}

--TODO: also make interactveProofStep
interactiveProofPreread :: KB -> [(KB,OpenTerm)] -> IntBindMonQuanT IO ()
interactiveProofPreread solvekb goals = do {
  interactiveProof' solvekb goals;
  lift3 $ putStrLn "Original goals:";
  aplGoals <- applyBindingsAll (snd <$> goals);
  sequence $ (lift3.putStrLn.oTToString) <$> aplGoals;
  return ()
}

interactiveProof' :: KB -> [(KB,OpenTerm)] -> IntBindMonQuanT IO ()
interactiveProof' solvekb goals = return goals >>=
                          propagateIteratingDepth >>=
                          --propagateProof >>=
                          --propagateProof' solvekb >>=
                          interactiveProof'' solvekb

instantiateGoals :: (Monad m) => [(KB,OpenTerm)] -> IntBindMonQuanT m [(KB,OpenTerm)]
instantiateGoals goals = sequence [do {
  --TODO: the KB might also need to get its universals applied at some point
  g <- instantiateUniversality gs;
  g' <- applyBindings g;
  return (kb, g')
} | (kb, gs) <- goals]

interactiveProof'' :: KB -> [(KB,OpenTerm)] -> IntBindMonQuanT IO ()
interactiveProof'' _ []  = return ()
interactiveProof'' solvekb goals = do {
  printState goals;
  possm <- proofPossibilities goals;

  lift3 $ putStrLn $ "Please enter step index:";

  possmlen <- return $ possMapLength possm;

  idx <- lift3 $ readLn;
  lift3 $ putStrLn "" >> putStrLn "" >> putStrLn "">> putStrLn "";
  if (0 <= idx) && (idx < possmlen)
  then applyProofAction possm idx >>= interactiveProof' solvekb
  else (lift3 $ putStrLn "invalid Index...") >> interactiveProof' solvekb goals
}

printState :: [(KB,OpenTerm)] -> IntBindMonQuanT IO ()
printState goals = do {
  possm <- proofPossibilities goals;
  printProofPossMap (possMapToIndices possm);
}

applyProofAction :: (Monad m) => GoalToPossMap m -> Int -> IntBindMonQuanT m [(KB,OpenTerm)]
applyProofAction possm idx = do {
  (newGoals, oldG) <- snd $ possMapGetIdx idx possm;
  (kb, oldgoal) <- return $ possMapGetKeyWithIdx idx possm;
  (prems, oldgoal') <- matchClauseStructure oldgoal;
  oldGoalsKB <- return $ map fst $ possMapRemoveKeyWithIdx idx possm;
  newGoalsKB <- return $ [((clauseFromList <$> return <$> prems)++kb, g) | g <- newGoals];
  return (newGoalsKB ++ oldGoalsKB)
}

--propagateIteratingDepth :: (Monad m) => [(KB,OpenTerm)] -> IntBindMonQuanT m [(KB,OpenTerm)]
propagateIteratingDepth :: [(KB,OpenTerm)] -> IntBindMonQuanT IO [(KB,OpenTerm)]
propagateIteratingDepth = propagateIteratingDepth' 0

--propagateIteratingDepth' :: (Monad m) => Int -> [(KB,OpenTerm)] -> IntBindMonQuanT m [(KB,OpenTerm)]
propagateIteratingDepth' :: Int -> [(KB,OpenTerm)] -> IntBindMonQuanT IO [(KB,OpenTerm)]
propagateIteratingDepth' n goals = catchE (do {
    goals' <- propagateDepth n goals;

    (lift3.putStrLn) $ "\n\n\n\n\n(depth "++(show n)++" after propagation)<><><><><><><>";
    printState goals';

    if null goals'
      then return goals'
      else throwE (CustomError "Not all goals fulfilled") --Looks dirty, but isn't. This is better for updating n
      --TODO: This fails if after applying several singletonians, there is no singletonian left to applied, but then throws away the applications! This cannot happen!
  }) (const $ propagateIteratingDepth' (n+1) goals)

propagateDepth :: (Monad m) => Int -> [(KB, OpenTerm)] -> IntBindMonQuanT m [(KB, OpenTerm)]
propagateDepth n goals =  preparationSequence goals >>=
                          propagateDepthAfterInit n

propagateDepthAfterInit :: (Monad m) => Int -> [(KB,OpenTerm)] -> IntBindMonQuanT m [(KB,OpenTerm)]
propagateDepthAfterInit _ [] = return []
--TODO: Add termination criterion where it is known no goal can succeed...in this case iteration can be stopped.
propagateDepthAfterInit 0 goals = return goals {-should stop, but should not fail! Branch might still be alive!-}{-throwE (CustomError "insufficient fuel!")-}
propagateDepthAfterInit n goals = do {
  possm <- (bakeMap <$> possMapToIndices <$> proofPossibilities goals);
  --TODO: somehow check whether the map has even changed in the first place...
  possm' <- reduceMap [(goal, [action >>= propagateDepth (n-1) | action <- possibs] ) | (goal, possibs) <- possm];
  {-
  --this was an attempt to apply rules already when they are not quite fix, to favour short solutions. Problem: There is no backtracking when things go wrong, so the solution space si eternally fixed.
  possmred <- reduceMap [(goal, [action >>= propagateDepth (n-1) >>= (\x -> guard ((not.null) x) >> return x) | action <- possibs] ) | (goal, possibs) <- possm];
  -}

  --traceShowM (n,possMapLength possm, possMapLength possm');

  if possMapHasNull possm'
    then throwE (CustomError "unprovable goals")
  else if null possm'
    then return []
    else catchE (applySingleton possm' {-possmred-} >>= propagateDepth n) (const $ return goals) ; --TODO: WARNING: This might not terminate...no fuel consumed for propagation step
    --TODO: Is there a way here to state that not all goals have to be redone after this?
    --TODO: Make alternative termination by saying all possibilities are known (and one can be chosen freely)
}

applySingleton :: (Monad m) => (GoalToNextStateMap m) -> IntBindMonQuanT m [(KB,OpenTerm)]
applySingleton possm = do {
  midx <- return $ possMapIndexOfFirstSingleton possm;
  case midx of
    Just idx -> possMapGetIdx idx possm
    Nothing -> throwE (CustomError "No singleton possibilities")
}

bakeMap :: (Monad m) => (IdxGoalToPossMap m) -> (GoalToNextStateMap m)
bakeMap possm = [(goal, [applyProofAction (possMapRemIdx possm) idx | (idx,_) <- idxpossibs]) | (goal, idxpossibs) <- possm]

reduceMap :: (Monad m) => (GoalToNextStateMap m) -> IntBindMonQuanT m (GoalToNextStateMap m)
reduceMap possm = sequence [do {
  newpossibs <- allSucceeding (map (\x -> x >> return x) possibs);
  return (goal, newpossibs)
} | (goal, possibs) <- possm]

proofPossibilities :: (Monad m) => [(KB,OpenTerm)] -> IntBindMonQuanT m (GoalToPossMap m)
proofPossibilities kbgoals = sequence [do {
  bwp <- backwardPossibilities kb g; --backwardPossibilitiesMatchClause
  return ((kb,g), bwp)
} | (kb,g) <- kbgoals]


propagateProof' :: (Monad m) => KB -> [(KB, OpenTerm)] -> IntBindMonQuanT m [(KB, OpenTerm)]
propagateProof' _ [] = return []
propagateProof' solvekb goals = propagateProofMETA solvekb goals;

preparationSequence :: (Monad m) => [(KB, OpenTerm)] -> IntBindMonQuanT m [(KB, OpenTerm)]
preparationSequence goals = instantiateGoals goals >>=
                            applySUQGoals >>=
                            applyImplicationGoals

propagateProof :: (Monad m) => [(KB, OpenTerm)] -> IntBindMonQuanT m [(KB, OpenTerm)]
propagateProof goals =  preparationSequence goals >>=
                        propagateProofAfterInit

propagateProofAfterInit :: (Monad m) => [(KB, OpenTerm)] -> IntBindMonQuanT m [(KB, OpenTerm)]
propagateProofAfterInit goals = do {
  possm <- proofPossibilities goals;
  midx <- return $ possMapIndexOfFirstSingleton possm;
  case midx of
    Just idx -> applyProofAction possm idx >>=
                propagateProof
    Nothing -> preparationSequence goals
}


--returns the propagated step with the META goal, together with the position of the META deduced next state.
--TODO: problem: there is no universal solving KB
--TODO: assignments of the solve predicate need to be applied to the real state
propagateProofMETA :: (Monad m) => KB -> [(KB, OpenTerm)] -> IntBindMonQuanT m [(KB, OpenTerm)]
propagateProofMETA solvekb goals  = do {
  qg <- applyBindings (goalsToTerm goals) >>= quoteTermVP;
  solveOutState <- lift $ freshVar;
  solvetrm <- return $ olist [con SOLVE, qg, solveOutState];
  unquotgoal <- lift $ freshVar;
  unquotetrm <- return $ olist [con UNQUOTE, solveOutState, unquotgoal];
  newgoals <- propagateProof ((solvekb, unquotgoal):(solvekb, unquotetrm):(solvekb, solvetrm): []); -- goals);
  --we'll do the infinite recursive call later...
  --if anythingChanged
  --  then propagateProofMETA newgoals
  --  else return (newgoals, solveOutState)
  return newgoals
}

{-
printGoalToNextStateMap :: (IdxGoalToNextStateMap IO) -> IntBindMonQuanT IO ()
printGoalToNextStateMap mp = void $ sequence [ do {

} | (goal, branches) <- mp]
-}

printProofPossMap :: (IdxGoalToPossMap IO) -> IntBindMonQuanT IO ()
printProofPossMap mp = void $ sequence [ do {
  aplgoal <- applyBindings goal;
  aplkb <- applyKB kb;
  kbToFormatStringVP aplkb >>= (lift3.putStrLn);
  lift3 $ putStrLn "       ------";
  gstring <- oTToStringVP aplgoal;
  lift3 $ putStrLn $ "goal ("++gstring++")       -- ("++ (show $ length poss) ++ " possibilitie(s))";
  sequence [do {
            cls' <- applyClause cls;
            clsstring <- clauseToStringVP cls';
            lift3 $ putStrLn $ "("++(show idx)++") "++ clsstring
            }| (idx, (cls, _)) <- poss];
  lift3 $ putStrLn "---------->>>>>>>>>>";
} | ((kb, goal), poss) <- mp]




possMapToIndices :: PossMap a b -> PossMap a (Int, b)
possMapToIndices = possMapToIndices' 0

possMapToIndices' :: Int -> PossMap a b -> PossMap a (Int, b)
possMapToIndices' _ [] = []
possMapToIndices' leastUnused ((x,lst):rest) = (x, zip [leastUnused ..] lst) : (possMapToIndices' (leastUnused + (length lst)) rest)

possMapGetIdx :: Int -> PossMap a b -> b
possMapGetIdx idx m = (possMapToSndLst m) !! idx

possMapToSndLst :: PossMap a b -> [b]
possMapToSndLst m = concatMap snd m

possMapLength :: PossMap a b -> Int
possMapLength = length.possMapToSndLst

possMapIndexOfFirstSingleton :: PossMap a b -> Maybe Int
possMapIndexOfFirstSingleton m = possMapIndexOfFirstSingleton' m 0
possMapIndexOfFirstSingleton' :: PossMap a b -> Int -> Maybe Int
possMapIndexOfFirstSingleton' [] idx = Nothing
possMapIndexOfFirstSingleton' ((a, bs) : lst) idx =
                                if isSingleton bs
                                then Just idx
                                else possMapIndexOfFirstSingleton' lst (idx + (length bs))


--TODO: DIRTY!
possMapRemoveKeyWithIdx :: Int -> PossMap a b -> PossMap a b
possMapRemoveKeyWithIdx idx [] = []
possMapRemoveKeyWithIdx idx ((a, bs):lst) = if idx < (length bs)
                                            then lst
                                            else (a, bs) : (possMapRemoveKeyWithIdx (idx - (length bs)) lst)

possMapGetKeyWithIdx :: Int -> PossMap a b -> a
possMapGetKeyWithIdx idx [] = error "index not in the map"
possMapGetKeyWithIdx idx ((a, bs):lst) = if idx < (length bs)
                                        then a
                                        else (possMapGetKeyWithIdx (idx - (length bs)) lst)

possMapRemIdx :: PossMap a (b,c) -> PossMap a c
possMapRemIdx possm = [(g,[k | (_,k) <- ks]) | (g,ks) <- possm]

possMapHasNull :: PossMap a b -> Bool
possMapHasNull possm = any null (snd <$> possm)

--TODO: could that whole possibility and KB thing be done with trees? I mean...kinda should really...Inner nodes are premises, leafs are goals...multiple possibilities and stuff can be similar...

--Single goal:
{-
type Conj = Set
type Disj = Set


apply ::kb -> goal -> Int -> mT m (Conj (kb, goal))

proofPossibilities :: kb -> goal -> mT m (Disj (Conj (kb, goal)))

interactiveApply :: kb -> goal -> mT IO (Conj (kb, goal))
-}
--multi goal (here, the goal is automatically split by conjunction. Conjunctions are done in parallel, which is important for automated reasoning. Implications create new kbs and are generally handled by splitting the program, disjunctions are object to interaction unless resolved by propagation)



--can't all operators just have programming meaning? Conjunction as parallel splitting, disjunction as interaction and implication as state copying?
