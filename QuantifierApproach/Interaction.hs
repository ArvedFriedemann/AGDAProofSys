module Interaction where

import TermData
import TermFunctions
import InferenceRules
import Util
import Printing
import Control.Unification
import Control.Monad

type Conj a = [a]
type Disj a = [a]

type PossMap a b = [(a,[b])]
type GoalToPossMap m = PossMap (KB,OpenTerm) (Clause, IntBindMonQuanT m Clause)
type IdxGoalToPossMap m = PossMap (KB,OpenTerm) (Int, (Clause, IntBindMonQuanT m Clause))

--TODO: also make interactveProofStep
interactiveProof :: [(KB,OpenTerm)] -> IntBindMonQuanT IO ()
interactiveProof goals = do {
  possm <- proofPossibilities goals;
  printProofPossMap (possMapToIndices possm);

  idx <- lift3 $ readLn;
  possmlen <- return $ possMapLength possm;
  if (0 >= idx) && (idx < possmlen)
  then do {
    (newGoals, oldG) <- snd $ possMapGetIdx idx possm;
    (kb, oldgoal) <- return $ possMapGetKeyWithIdx idx possm;
    (prems, oldgoal') <- matchClauseStructure oldgoal;
    oldGoalsKB <- return $ map fst $ possMapRemoveKeyWithIdx idx possm;
    newGoalsKB <- return $ [((clauseFromList <$> return <$> prems)++kb, g) | g <- newGoals];
    interactiveProof (newGoalsKB ++ oldGoalsKB)
  }
  else (lift3 $ putStrLn "invalid Index...") >> interactiveProof goals
}


proofPossibilities :: (Monad m) => [(KB,OpenTerm)] -> IntBindMonQuanT m (GoalToPossMap m)
proofPossibilities kbgoals = sequence [do {
  bwp <- backwardPossibilities kb g;
  return ((kb,g), bwp)
} | (kb,g) <- kbgoals]


printProofPossMap :: (IdxGoalToPossMap IO) -> IntBindMonQuanT IO ()
printProofPossMap mp = void $ sequence [ do {
  aplgoal <- applyBindings goal;
  lift3 $ putStrLn $ "goal ("++(oTToString aplgoal)++")";
  sequence [applyClause cls >>=
            \cls' -> lift3 $ putStrLn $ "("++(show idx)++") "++(clauseToString cls')
            | (idx, (cls, _)) <- poss];
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
