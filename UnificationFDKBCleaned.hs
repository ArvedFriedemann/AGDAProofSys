module UnificationFDKBCleaned where

import UnificationFDApproach
import Control.Unification
import Control.Unification.Types
import Control.Unification.IntVar
import Control.Monad.Trans
import Control.Monad.Trans.Except
import Data.List

type Clause = ([OpenTerm], OpenTerm)
type KB = [Clause]

cprem :: Clause -> [OpenTerm]
cprem (prems, _) = prems

cpost :: Clause -> OpenTerm
cpost (_, post) = post

clauseToList :: Clause -> [OpenTerm]
clauseToList (lst, p) = p:lst

clauseToBWList :: Clause -> [OpenTerm]
clauseToBWList (lst, p) = lst++[p]

listToClause :: [OpenTerm] -> Clause
listToClause (x:xs) = (xs, x)

clauseToString :: Clause -> String
clauseToString c = concat $ intersperse "->" (((\x -> "("++x++")").oTToString) <$> (clauseToBWList c))

transformAsListM :: (Monad m) => ([OpenTerm] -> m [OpenTerm]) -> Clause -> m Clause
transformAsListM fkt c = do {
  trans <- fkt (clauseToList c);
  return (listToClause trans);
}

--copies the clause terms, matches them and returns the assigned clauses
matchClause :: (Monad m) => OpenTerm -> Clause -> IntBindMonT m Clause
matchClause goal clause = do {
  newclause@(newgoals, post) <- transformAsListM freshenAll clause;
  subs <- subsumes post goal;
  if subs
  then do {
    unify post goal;
    transformAsListM applyBindingsAll newclause
  }
  else (lift freeVar) >>= (\vd -> throwE (occursFailure vd goal)) --TODO: again, super hacky

}

--gives for a goal all possible new branches with goals, the new assignment and the action for when taking the branch.
backwardPossibilities :: (Monad m) => KB -> OpenTerm -> IntBindMonT m [(Clause, IntBindMonT m Clause)]
backwardPossibilities kb goal = possibleActions [matchClause goal c | c <- kb]

--propagates all goals that have only a single rule match. Returns the next list of goals (they could be further propagated). Also returns whether anything has changed at all.
propagateProofStep' :: (Monad m) => KB -> [OpenTerm] -> IntBindMonT m ([OpenTerm],Bool)
propagateProofStep' kb goals = do {
  branches <- zip goals <$> (sequence $ [backwardPossibilities kb g | g <- goals]);
  (singletons, multitons) <- return $ partition (isSingleton.snd) branches;
  multitonGoals <- return $ fst <$> multitons;
  singletonGoals <- return $ fst <$> singletons;
  singletonActions <- return $ (snd <$> (head <$> (snd <$> singletons)));
  newclauses <- sequence $ singletonActions;
  return $ ((concat $ cprem <$> newclauses) ++ (multitonGoals), (not.null) singletons);
}

--propagates the proof until no further steps can be made
propagateProof :: (Monad m) => KB -> [OpenTerm] -> IntBindMonT m [OpenTerm]
propagateProof kb goals = do {
  (goals', hasChanged) <- propagateProofStep' kb goals;
  if hasChanged
  then propagateProof kb goals'
  else return goals
}

interactiveProof' :: KB -> [OpenTerm] -> IntBindMonT IO [OpenTerm]
interactiveProof' kb goals = do {
  lift2 $ putStrLn "KB:";
  lift2 $ sequence $ (putStrLn.clauseToString) <$> kb;
  lift2 $ putStrLn "Goals:";
  lift2 $ sequence $ (putStrLn.oTToString) <$> goals;

  possibilities <- concat <$> (sequence [backwardPossibilities kb g | g <- goals]);
  possibClauses <- return $ fst <$> possibilities;
  possibActions <- return $ snd <$> possibilities;

  lift2 $ putStrLn "Steps:";
  lift2 $ sequence [putStrLn $ "("++(show i)++") "++(clauseToString c) | (i,c) <- zip [0..] possibClauses];


  return goals --TODO!
}



allSucceeding :: (Monad m) => [IntBindMonT m a] -> IntBindMonT m [a]
allSucceeding mons = (map fst) <$> possibleActions mons

--tries out every action (always backtracking to the original state) and returns the action paired with the result they'd give. A generalised lookout or allSucceeding. BACKTRACKS IN ALL CASES!
possibleActions:: (Monad m) => [IntBindMonT m a] -> IntBindMonT m [(a,IntBindMonT m a)]
possibleActions acts = concat <$> (sequence [lookoutCatch ((\r -> (r, m)) <$> m) | m <- acts])

isSingleton :: [a] -> Bool
isSingleton [x] = True
isSingleton _   = False


{-
Problems:
original idea was to have a goal with constrained variables and then find a path through the KB. This path is the proof. Technically, KB should be enhanceable during the proof. Problem: search should depend on the whole available knowledge, not just one goal.

When using the andorra style proof search strategy, a proof should be created. However andorra should just be an evaluation strategy. Maybe set the strategy completely arbitrary? But what to evaluate in that case?

Yes, Andorra just just stay the evaluation strategy, and everything else is on top.
-}
