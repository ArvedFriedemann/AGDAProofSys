module UnificationFDKBCleaned where

import UnificationFDApproach
import Control.Unification
import Control.Unification.Types
import Control.Unification.IntVar
import Control.Monad.Trans
import Control.Monad.Trans.Except
import Control.Monad
import Data.List
import Debug.Trace

type Clause = ([OpenTerm], OpenTerm)
type KB = [Clause]

mapPrems :: ([OpenTerm] -> [OpenTerm]) -> Clause -> Clause
mapPrems fkt (prems,post) = (fkt prems, post)

cprem :: Clause -> [OpenTerm]
cprem (prems, _) = prems

cpost :: Clause -> OpenTerm
cpost (_, post) = post

clauseToList :: Clause -> [OpenTerm]
clauseToList (lst, p) = lst++[p]

listToClause :: [OpenTerm] -> Clause
listToClause lst = (init lst, last lst)

clauseToString :: Clause -> String
clauseToString c = concat $ intersperse "->" (((\x -> "("++x++")").oTToString) <$> (clauseToList c))

transformAsListM :: (Monad m) => ([OpenTerm] -> m [OpenTerm]) -> Clause -> m Clause
transformAsListM fkt c = do {
  trans <- fkt (clauseToList c);
  return (listToClause trans);
}

--copies the clause terms, matches them and returns the assigned clauses
matchClause :: (Monad m) => OpenTerm -> Clause -> IntBindMonT m Clause
--matchClause (UTerm (CONST BOT)) clause = do { TODO: if bot were treated special, this is where it went}
matchClause goal clause = do {
  newclause@(newgoals, post) <- transformAsListM freshenAll clause;
  --
  --traceM $ "Merging (" ++ (oTToString post) ++ ") and (" ++ (oTToString goal) ++ ")";
  unify post goal;
  transformAsListM applyBindingsAll newclause
  --
  {-
  subs <- subsumes post goal;
  if subs
  then do {
    unify post goal;
    transformAsListM applyBindingsAll newclause
  }
  else (lift freeVar) >>= (\vd -> throwE (occursFailure vd goal)) --TODO: again, super hacky
  -}
}

--gives for a goal all possible new branches with goals, the new assignment and the action for when taking the branch.
backwardPossibilities :: (Monad m) => KB -> OpenTerm -> IntBindMonT m [(Clause, IntBindMonT m Clause)]
backwardPossibilities kb goal = do {
  gclause <- matchClauseStructure goal;
  case gclause of
    (prems,post) -> do {
      prems' <- sequence $ matchClauseStructure <$> prems;
      possibleActions [matchClause post c >>=
                  (\c' -> return $ ((\c'' -> oplist (con IMPL) (prems ++ [c''])) <$> (cprem c'),
                                             oplist (con IMPL) (prems ++ [cpost c'])))
                                    | c <- prems' ++ kb]
    }
}
--propagates all goals that have only a single rule match. Returns the next list of goals (they could be further propagated). Also returns whether anything has changed at all.
--For safety, this only propagates the first singletonian! (they sometimes interfere when conflict arises)
propagateProofStep' :: (Monad m) => KB -> [OpenTerm] -> IntBindMonT m ([OpenTerm],Bool)
propagateProofStep' kb goals = do {
  branches <- zip goals <$> (sequence $ [backwardPossibilities kb g | g <- goals]);
  (singletons, multitons) <- return $ partition (isSingleton.snd) branches;
  multitonGoals <- return $ fst <$> multitons;
  singletonGoals <- return $ fst <$> singletons;
  singletonActions <- return $ (snd <$> (head <$> (snd <$> singletons)));
  if not $ null singletons
  then do {
    --this ensures that only one singleton goal is applied at a time (better for conflict handling)
    newclause <- head $ singletonActions;
    return ((cprem newclause) ++ (tail singletonGoals) ++ multitonGoals, True)
  }
  else return (multitonGoals, False)
}

--filters the list of goals by goals declaring an equality and unifies them. Returns whether any occurred.
unifyEQGoals :: (Monad m) => [OpenTerm] -> IntBindMonT m Bool
unifyEQGoals trms = do {
  matches <- allSucceeding $ (matchBinConst EQT) <$> trms;
  sequence $ (uncurry unify) <$> matches;
  return $ (not.null) matches
}


--checks if the given term is a left-associative binary operator of the given constant. If that is the case it returns the two arguments. Does not apply the bindings!
matchBinConst :: (Monad m) => Constant -> OpenTerm -> IntBindMonT m (OpenTerm,OpenTerm)
matchBinConst cst term = do {
                              a <- lift $ freshVar;
                              b <- lift $ freshVar;
                              ot <- return $ olist [a, con cst, b];
                              sub <- subsumes ot term;
                              if sub
                              then unify ot term >> applyBindingsAll [a,b] >>= (\[a',b'] -> return (a',b'));
                              else (lift freeVar) >>= (\vd -> throwE (occursFailure vd term)) --TODO: again, super hacky
                            }

matchBinConstLAssocList :: (Monad m) => Constant -> OpenTerm -> IntBindMonT m [OpenTerm]
matchBinConstLAssocList cst term = catchE (do {
  (a,b) <- matchBinConst cst term;
  lst <- matchBinConstLAssocList cst a;
  return $ lst ++ [b];
}) (const $ return [term])

matchClauseStructure :: (Monad m) => OpenTerm -> IntBindMonT m Clause
matchClauseStructure trm = listToClause <$> (matchBinConstLAssocList IMPL trm)

--propagates the proof until no further steps can be made
propagateProof :: (Monad m) => KB -> [OpenTerm] -> IntBindMonT m [OpenTerm]
propagateProof kb goals = do {
  (goals', hasChanged) <- propagateProofStep' kb goals;
  --too hacky. Equality should just be modeled using the axiom a = a.
  --hasChangedEQ <- unifyEqGoals goals';
  --goals'' <- filterM (null <$> (matchBinConst EQT)) goals'
  if hasChanged
  then propagateProof kb goals'
  else return goals
}

--returns the original goals!
interactiveProof :: KB -> [OpenTerm] -> IntBindMonT IO ()
interactiveProof kb goals = do {
  interactiveProof'' kb goals;
  lift2 $ putStrLn "Initial Goals:";
  goals' <- applyBindingsAll goals;
  void $ lift2 $ sequence [putStrLn $ oTToString g | g <- goals']
}

interactiveProof'' :: KB -> [OpenTerm] -> IntBindMonT IO [OpenTerm]
interactiveProof'' kb goals = do {
  --goals' <- propagateProof kb goals;
  goals' <- return goals;
  if null goals'
  then do {
    lift2 $ putStrLn "Congratulations! All goals fulfilled!";
    return []
  }
  else interactiveProof' kb goals'
}

interactiveProof' :: KB -> [OpenTerm] -> IntBindMonT IO [OpenTerm]
interactiveProof' kb goals = do {
  lift2 $ putStrLn "KB:";
  lift2 $ sequence $ (putStrLn.clauseToString) <$> kb;
  lift2 $ putStrLn "Goals:";
  goalsAppl <- applyBindingsAll goals;
  lift2 $ sequence $ (putStrLn.oTToString) <$> goalsAppl;

  possByGoal   <- zip goals <$> (sequence [backwardPossibilities kb g | g <- goals]);
  case find (\(g,poss) -> null poss) possByGoal of
    Just (g,poss) -> do {
      lift2 $ putStrLn $ "goal (" ++ (oTToString g) ++ ") unprovable";
      fail "unprovable"}
    Nothing -> do {
      possibilities <- return $ concat (snd <$> possByGoal);
      possibClauses <- return $ fst <$> possibilities;
      possibActions <- return $ snd <$> possibilities;

      lift2 $ putStrLn "Steps:";
      sequence [do {
            g' <- applyBindings g;
            lift2 $ putStrLn $ "goal (" ++ (oTToString g')++"): ";
            lift2 $ sequence [putStrLn $ "("++(show i)++") "++(clauseToString $ fst c) | (i,c) <- zip [start..end] brchs]}
        | (g,brchs, start, end) <- giveIdxRange possByGoal];

      idx <- lift2 $ readLn;
      if 0 <= idx && idx < (length possibilities)
      then do {
        --first snd is for the map, second for the action (it comes attached with a clause for output)
        (prems, post) <- snd $ snd $ pickFromMap possByGoal idx;
        interactiveProof'' kb $ prems++(map fst $ removeIdx possByGoal idx)
      };
      else do {
        lift2 $ putStrLn "Invalid Index...";
        interactiveProof'' kb goals
      };

    }
}



allSucceeding :: (Monad m) => [IntBindMonT m a] -> IntBindMonT m [a]
allSucceeding mons = (map fst) <$> possibleActions mons

--tries out every action (always backtracking to the original state) and returns the action paired with the result they'd give. A generalised lookout or allSucceeding. BACKTRACKS IN ALL CASES!
possibleActions:: (Monad m) => [IntBindMonT m a] -> IntBindMonT m [(a,IntBindMonT m a)]
possibleActions acts = concat <$> (sequence [lookoutCatch ((\r -> (r, m)) <$> m) | m <- acts])

isSingleton :: [a] -> Bool
isSingleton [x] = True
isSingleton _   = False

pickFromMap :: [(a,[b])] -> Int -> (a,b)
pickFromMap [] i = error "invalid index"
pickFromMap ((a,lst):xs) i = if i < (length lst)
                              then (a,lst !! i)
                              else pickFromMap xs (i - (length lst))

removeIdx :: [(a,[b])] -> Int -> [(a,[b])]
removeIdx [] _ = []
removeIdx ((a,lst):xs) i = if i < (length lst)
                              then xs
                              else (a,lst) : (removeIdx xs (i - (length lst)) )

giveIdxRange :: [(a,[b])] -> [(a,[b],Int,Int)]
giveIdxRange mp = giveIdxRange' 0 mp

giveIdxRange' :: Int -> [(a,[b])] -> [(a,[b],Int,Int)]
giveIdxRange' oneHigher [] = []
giveIdxRange' oneHigher ((a,lst):xs) = (a,lst,oneHigher,oneHigher + (length lst) - 1) :
                                        (giveIdxRange' (oneHigher + (length lst)) xs)
{-
Problems:
original idea was to have a goal with constrained variables and then find a path through the KB. This path is the proof. Technically, KB should be enhanceable during the proof. Problem: search should depend on the whole available knowledge, not just one goal.

When using the andorra style proof search strategy, a proof should be created. However andorra should just be an evaluation strategy. Maybe set the strategy completely arbitrary? But what to evaluate in that case?

Yes, Andorra just just stay the evaluation strategy, and everything else is on top.
-}
