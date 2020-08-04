module UnificationFDKB where

import UnificationFDApproach
import Control.Unification
import Control.Unification.Types
import Control.Unification.IntVar
import Control.Monad.Trans
import Control.Monad.Trans.Except
import Data.Either
import Debug.Trace
import Data.List

type IntKB = ([OpenTerm], [(OpenTerm, OpenTerm)]) --facts and rules

implications :: (Monad m) => IntKB -> IntBindMonT m [OpenTerm]
implications (facts, rules) = allSucceeding [lookout $ applyRule f r | f <- facts, r <- rules]

premises :: (Monad m) => [(OpenTerm, OpenTerm)] -> OpenTerm -> IntBindMonT m [OpenTerm]
premises rules goal = allSucceeding [lookout $ reverseRule r goal | r <- rules]

applyRule :: (Monad m) => OpenTerm -> (OpenTerm, OpenTerm) -> IntBindMonT m OpenTerm
applyRule fact (pre,post) = do {
  lst <- freshenAll [pre,post];
  case lst of
    [pre',post'] -> do {
      unify fact pre';
      applyBindings post'
    }
}

reverseRule :: (Monad m) => (OpenTerm, OpenTerm) -> OpenTerm -> IntBindMonT m OpenTerm
reverseRule (pre,post) fact = do {
  lst <- freshenAll [pre,post];
  case lst of
    [pre',post'] -> do {
      unify fact post';
      applyBindings pre'
    }
}

matchImpl :: (Monad m) => OpenTerm -> IntBindMonT m (OpenTerm, OpenTerm)
matchImpl t = do {v1 <- lift freshVar; v2 <- lift freshVar;
  impltrm <- return $ list [v1, scon "->", v2];
  sub <- subsumes impltrm t;
  vd <- lift $ freeVar;
  if sub then return () else throwE (occursFailure vd impltrm); --TODO: this is super hacky. But subsumes check is necessary.
  unify t impltrm;
  pre <- applyBindings v1;
  post <- applyBindings v2;
  return (pre,post)
}

--right associative version
--matchImplLst :: (Monad m) => OpenTerm -> IntBindMonT m ([OpenTerm], OpenTerm)
--matchImplLst t = lookout $ catchE (do {
--                          (pre,post) <- matchImpl t;
--                          (pres, post') <- matchImplLst post;
--                          return (pre:pres, post')})
--                          (const $ return ([],t))

--TODO: this is a hack. Implication should not be left associative!
matchImplLst :: (Monad m) => OpenTerm -> IntBindMonT m ([OpenTerm], OpenTerm)
matchImplLst t = lookout $ catchE (do {
                          (pre,post) <- matchImpl t;
                          (pres, post') <- matchImplLst pre;
                          return (pres++[post'], post)})
                          (const $ return ([],t))

getImpls :: (Monad m) => [OpenTerm] -> IntBindMonT m [(OpenTerm,OpenTerm)]
getImpls ts = allSucceeding $ (lookout.matchImpl) <$> ts

getImplsLst :: (Monad m) => [OpenTerm] -> IntBindMonT m [([OpenTerm],OpenTerm)]
getImplsLst ts = sequence $ (lookout.matchImplLst) <$> ts

--gives lookout old and new goals for match against goal. Additionally gives the original rule to apply it again if necessary.
implLstAgainstGoal :: (Monad m) => [([OpenTerm],OpenTerm)] -> OpenTerm -> IntBindMonT m [(OpenTerm, [OpenTerm], ([OpenTerm], OpenTerm) )]
implLstAgainstGoal rules goal = allSucceeding $ [do {
                      oldgoal <- unify post goal >>= applyBindings;
                      newgoals <- sequence $ applyBindings <$> prems;
                      return (oldgoal, newgoals, (prems, post))
                      } | (prems, post) <- rules]

allSucceeding :: (Monad m) => [IntBindMonT m a] -> IntBindMonT m [a]
allSucceeding mons = (map fst) <$> possibleActions mons

splitSucceeding :: (Monad m) => (OpenTerm -> IntBindMonT m a) -> [OpenTerm]
                                -> IntBindMonT m ([a],[OpenTerm])
splitSucceeding fkt ts = do {
  e <- sequence [catchE (Left <$> fkt t) (const $ return $ Right t) | t <- ts];
  return (lefts e, rights e)
}

lookoutCatch :: (Monad m) => IntBindMonT m a -> IntBindMonT m [a]
lookoutCatch m = lookout $ catchE (return <$> m) (const $ return [])

--tries out every action (always backtracking to the original state) and returns the action paired with the result they'd give. A generalised lookout or allSucceeding. BACKTRACKS IN ALL CASES!
possibleActions:: (Monad m) => [IntBindMonT m a] -> IntBindMonT m [(a,IntBindMonT m a)]
possibleActions acts = concat <$> (sequence [lookoutCatch ((\r -> (r, m)) <$> m) | m <- acts])

--gives all possible merges of the goal with the facts, together with an optimised action that can apply that match to the state. The optimised action may only give a pointer to the correct term, the other two given terms have aplied bindings. The first term is the original factm the second the original goal and the third the new goal, all with applied bindings at their respective time of application.
possibleFactMerges :: (Monad m) => [OpenTerm] -> OpenTerm ->
                      IntBindMonT m [(IntBindMonT m OpenTerm, OpenTerm, OpenTerm, OpenTerm)]
possibleFactMerges kb goal = concat <$> (sequence $ [lookoutCatch $
                                        do {g' <- applyBindings goal;
                                            t' <- applyBindings t;
                                            act;
                                            g'' <- applyBindings goal;
                                            return (act, t', g', g'') }
                                          | (act, t) <- [(unify t goal, t) | t <- kb]])

--outputs are the action, the original rule, the original goal, the old goal after application, the new goal
--TODO: the implication match should be recursive, to get multiple new goals.
--possibleBWRuleMerges :: (Monad m) => [OpenTerm] -> OpenTerm ->
--                      IntBindMonT m [(IntBindMonT m OpenTerm, OpenTerm, OpenTerm, OpenTerm, OpenTerm)]
--possibleBWRuleMerges kb goal = concat <$> (sequence $ [lookoutCatch $
--                                        do {g' <- applyBindings goal;
--                                            t' <- applyBindings t;
--                                            pre <- act;
--                                            g'' <- applyBindings goal;
--                                            pre' <- applyBindings pre;
--                                            return (act, t', g', g'', pre') }
--                                          | (act, t) <- [(do {(pre,post) <- matchImpl t; unify post goal; return pre)}, t) | t <- kb]])
--

stdcrt :: (Monad m) => String -> ExceptT MError (IntBindingT Term m) OpenTerm
stdcrt = lift.createOpenTerm.stdrd

stdrd = binds.rt
testrules2 = map stdrd [("(a = b) -> (b = a)"),("(a ^ b) -> a"), ("(a ^ b) -> b")]
testfacts2 = map ((bindConst ["k","l"]).stdrd ) ["(k ^ (k k))", "l = k"]

test2 = runIntBind $ do {
  --t <- lift $ freshTermFromString' bounds "a -> (b b)";

  kbr <- sequence $ lift <$> createOpenTerm <$> testrules2;
  rules <- getImpls kbr;
  facts <- sequence $ lift <$> createOpenTerm <$> testfacts2;
  impls <- implications (facts, rules);
  return $ ppCTerm <$> giveNiceNames <$> fromOpenTerm <$> impls
}

testrules3 = map stdrd [("a ^ (a a)"),("(b b) ^ b"), ("a v b"), ("(a ^ b) -> a"), ("(a ^ b) -> b")]
testfacts3 = map ((bindConst ["k","l"]).stdrd ) ["a ^ b", "l = k"]

test3 = runIntBindT $ do {
  --t <- lift $ freshTermFromString' bounds "a -> (b b)";

  kbr <- sequence $ lift <$> createOpenTerm <$> testrules3;
  facts <- sequence $ lift <$> createOpenTerm <$> testfacts3;
  makeProofOld' kbr (head facts)
}

testrules4 = map stdrd [("(a v b) -> (a -> c) -> (b -> c) -> c")]
testfact4 = stdrd "a"

test4 = runIntBindT $ do {
  kbr <- sequence $ lift <$> createOpenTerm <$> testrules4;
  facts <- lift $ createOpenTerm testfact4;
  (prems,post) <- matchImplLst (head kbr);
  --TODO: This should give way mor premises...
  lift2 $ putStrLn "Original:";
  lift2 $ putStrLn $ oTToString (head kbr);
  lift2 $ putStrLn "Extracted:";
  lift2 $ sequence $ putStrLn <$> oTToString <$> prems;
  lift2 $ putStrLn $ oTToString post;
}

testrules5 = map stdrd ["a -> b -> (a ^ b)", "a -> (a v b)", "b -> (a v b)"]
testfacts5 = map stdrd ["a ^ b", "a v b"]

test5 = runIntBindT $ do {
  kbr <- sequence $ lift <$> createOpenTerm <$> testrules5;
  goals <- sequence $ lift <$> createOpenTerm <$> testfacts5;
  (kb', newgoals) <- {--return (kbr, goals);--}propagateProof kbr goals;
  makeProof kb' newgoals;
  --TODO: here, general rules are not copied yet. Once applied, they are changed in the KB.!
  --TODO! TODO! TODO!
  --TODO: also, for general rules, it might need to be the case that the posterior subsumes the goal...not hundret percent sure though.
}

--returns the proof state (kb and goals) after propagation.
propagateProof :: [OpenTerm] -> [OpenTerm] -> IntBindMonT IO ([OpenTerm], [OpenTerm])
propagateProof kb goals = do {
  impllst <- getImplsLst kb;
  newgoals <- concat <$> sequence [do {
      lst <- implLstAgainstGoal impllst goal;
      case lst of
        [] -> fail ("goal " ++ (oTToString goal) ++ "cannot be resolved.")
        [(_,_,(pres, post))] -> do {
                applyBindingsAll (post:pres);
                lst <- freshenAll (post:pres);
                case lst of
                  (post':pres') -> unify goal post' >> return pres'
                  _ -> fail "should not happen"
                }
        _ -> return [goal]
    } | goal <- goals];
  if (fromOpenTerm <$> newgoals) == (fromOpenTerm <$> goals)
    then return (kb, newgoals)
    else propagateProof kb newgoals
}

makeProof :: [OpenTerm] -> [OpenTerm] -> IntBindMonT IO ()
makeProof kb goals = do {
  impllst <- getImplsLst kb;
  sequence $ [
    do {
      gbind <- applyBindings goal;
      lift2 $ putStr $ "Goal: ";
      lift2 $ putStrLn $ oTToString gbind;
      lst <- implLstAgainstGoal impllst goal;
      lift2 $ putStrLn $ "Matches: ";
      sequence $ [(lift2 $ putStr (concat $ intersperse " ^ " [(oTToString p)| p <- newgoals])) >>
                   lift2 (putStrLn (" from "++(oTToString oldgoal)++""))|
                              (oldgoal, newgoals, _) <- lst];
      lift2 $ putStrLn "";
    }
    | goal <- goals
  ];
  return ()
}

makeProofOld':: [OpenTerm] -> OpenTerm -> IntBindMonT IO ()
makeProofOld' kb goal = do {
  axioms <- allSucceeding $ [(unify t goal >>= applyBindings) | t <- kb];
  (rules, facts) <- splitSucceeding (lookout.matchImpl) kb;
  impls <- implications (facts, rules);
  --newgoals <- premises rules goal;

  --t1 <- stdcrt "a ^ b";
  --t2 <- stdcrt "a ^ (a a)";

  lift2 $ putStrLn "Knowledge Base:";
  lift2 $ sequence [putStrLn $ oTToString fact | fact <- kb];
  lift2 $ putStrLn "Goal:";
  lift2 $ putStrLn $ oTToString goal;
  --TODO: For proper visuals, bindings need to be applied to the rule as well maybe...
  actions1 <- possibleFactMerges kb goal;
  actions2 <- possibleActions [(\u -> (u,(pre,post))) <$> (unify goal post >> applyBindings pre) | (pre,post) <- rules];
  actions3 <- possibleActions [(\u -> (u,(f,pre,post))) <$> (unify f pre >> applyBindings post) | (pre,post) <- rules, f <- kb];
  lift2 $ putStrLn "Axiom Actions:";
  lift2 $ sequence [putStrLn $ (show idx) ++ ": " ++ (oTToString o) ++ " from "++(oTToString t)++" and "++(oTToString g) | (idx, (_,t,g,o)) <- zip [1..] actions1];
  lift2 $ putStrLn "Reverse Rule Actions:";
  lift2 $ sequence [putStrLn $ (show idx) ++ ": " ++ (oTToString o) ++ " from "++(oTToString pre) ++ "->" ++(oTToString post) | (idx, ((o,(pre,post)),_)) <- zip [1..] actions2];
  lift2 $ putStrLn "Fact Implication Actions:";
  lift2 $ sequence [putStrLn $ (show idx) ++ ": " ++ (oTToString o) ++ " from "++(oTToString pre) ++ "->" ++(oTToString post) ++ " and " ++(oTToString f) | (idx, ((o,(f,pre,post)),_)) <- zip [1..] actions3];
  --lift2 $ putStrLn "Axioms:";
  --lift2 $ sequence $ (putStrLn.oTToString) <$> axioms;
  --lift2 $ putStrLn "Implications from DB:";
  --lift2 $ sequence $ (putStrLn.oTToString) <$> impls;
  --lift2 $ putStrLn "new goals:";
  --lift2 $ sequence $ (putStrLn.oTToString) <$> newgoals;
  --t <- lift $ freshTermFromString "a";
  --lift2 $ putStrLn "TADAAA!";
  return ()
}

lift2 :: (MonadTrans t1, MonadTrans t2, Monad m, Monad (t2 m)) =>
          m a -> t1 (t2 m) a
lift2 = lift.lift
