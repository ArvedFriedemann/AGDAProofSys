module Interaction where

import TermData
import TermFunctions
import InferenceRules
import SpecialMatches
import Util
import Printing

import Control.Unification
import Control.Monad
import Debug.Trace
import Data.List

type Conj a = [a]
type Disj a = [a]

type PossMap a b = [(a,[b])]
type GoalToPossMap m = PossMap (KB,OpenTerm) (Clause, IntBindMonQuanT m Clause)
type IdxGoalToPossMap m = PossMap (KB,OpenTerm) (Int, (Clause, IntBindMonQuanT m Clause))

interactiveProof :: [(RawKB,OpenTerm)] -> IntBindMonQuanT IO ()
interactiveProof goals = do  {
  goals' <- sequence $ [readRawKB kb >>= \kb' -> return (kb', gs) |(kb,gs) <- goals];
  interactiveProofPreread goals';
}

--TODO: also make interactveProofStep
interactiveProofPreread :: [(KB,OpenTerm)] -> IntBindMonQuanT IO ()
interactiveProofPreread goals = do {
  interactiveProof' goals;
  lift3 $ putStrLn "Original goals:";
  aplGoals <- applyBindingsAll (snd <$> goals);
  sequence $ (lift3.putStrLn.oTToString) <$> aplGoals;
  return ()
}

interactiveProof' :: [(KB,OpenTerm)] -> IntBindMonQuanT IO ()
interactiveProof' goals = return goals >>=
                          instantiateGoals >>=
                          --propagateProof >>=
                          --instantiateGoals >>=
                          interactiveProof''

instantiateGoals :: (Monad m) => [(KB,OpenTerm)] -> IntBindMonQuanT m [(KB,OpenTerm)]
instantiateGoals goals = sequence [do {
  --TODO: the KB might also need to get its universals applied at some point
  g <- instantiateUniversality gs;
  g' <- applyBindings g;
  return (kb, g')
} | (kb, gs) <- goals]

interactiveProof'' :: [(KB,OpenTerm)] -> IntBindMonQuanT IO ()
interactiveProof'' [] = return ()
interactiveProof'' goals = do {
  possm <- proofPossibilities goals;
  printProofPossMap (possMapToIndices possm);

  possmlen <- return $ possMapLength possm;

  idx <- lift3 $ readLn;
  if (0 <= idx) && (idx < possmlen)
  then applyProofAction possm idx >>= interactiveProof'
  else (lift3 $ putStrLn "invalid Index...") >> interactiveProof' goals
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

proofPossibilities :: (Monad m) => [(KB,OpenTerm)] -> IntBindMonQuanT m (GoalToPossMap m)
proofPossibilities kbgoals = sequence [do {
  bwp <- backwardPossibilitiesMatchClause kb g;
  return ((kb,g), bwp)
} | (kb,g) <- kbgoals]

propagateProof :: (Monad m) => [(KB, OpenTerm)] -> IntBindMonQuanT m [(KB, OpenTerm)]
propagateProof goals = do {
  possm <- proofPossibilities goals;
  midx <- return $ possMapIndexOfFirstSingleton possm;
  case midx of
    Just idx -> applyProofAction possm idx >>= instantiateGoals >>= propagateProof
    Nothing -> return goals
}

printProofPossMap :: (IdxGoalToPossMap IO) -> IntBindMonQuanT IO ()
printProofPossMap mp = void $ sequence [ do {
  aplgoal <- applyBindings goal;
  aplkb <- applyKB kb;
  lift3 $ putStrLn $ kbToFormatString aplkb;
  lift3 $ putStrLn $ "goal ("++(oTToString aplgoal)++")       -- ("++ (show $ length poss) ++ " possibilitie(s))";
  sequence [do {
            cls' <- applyClause cls;
            lift3 $ putStrLn $ "("++(show idx)++") "++(clauseToString cls')
            }| (idx, (cls, _)) <- poss];
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
