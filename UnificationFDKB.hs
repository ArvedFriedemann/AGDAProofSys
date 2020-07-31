module UnificationFDKB where

import UnificationFDApproach
import Control.Unification
import Control.Unification.Types
import Control.Unification.IntVar
import Control.Monad.Trans
import Control.Monad.Trans.Except
import Data.Either

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
  unify t (list [v1, scon "->", v2]);
  pre <- applyBindings v1;
  post <- applyBindings v2;
  return (pre,post)
}

getImpls :: (Monad m) => [OpenTerm] -> IntBindMonT m [(OpenTerm,OpenTerm)]
getImpls ts = allSucceeding $ (lookout.matchImpl) <$> ts

allSucceeding :: (Monad m) => [IntBindMonT m a] -> IntBindMonT m [a]
allSucceeding mons = (map fst) <$> possibleActions mons

splitSucceeding :: (Monad m) => (OpenTerm -> IntBindMonT m a) -> [OpenTerm]
                                -> IntBindMonT m ([a],[OpenTerm])
splitSucceeding fkt ts = do {
  e <- sequence [catchE (Left <$> fkt t) (const $ return $ Right t) | t <- ts];
  return (lefts e, rights e)
}

--tries out every action (always backtracking to the original state) and returns the action paired with the result they'd give. A generalised lookout or allSucceeding. BACKTRACKS IN ALL CASES!
possibleActions:: (Monad m) => [IntBindMonT m a] -> IntBindMonT m [(a,IntBindMonT m a)]
possibleActions acts = concat <$> (sequence [lookout $ catchE ((\r -> [(r, m)]) <$> m) (const $ return []) | m <- acts])


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
  makeProof' kbr (head facts)
}

makeProof':: [OpenTerm] -> OpenTerm -> IntBindMonT IO ()
makeProof' kb goal = do {
  axioms <- allSucceeding $ [(unify t goal >>= applyBindings) | t <- kb];
  --(rules, facts) <- splitSucceeding (lookout.matchImpl) kb;
  --impls <- implications (facts, rules);
  --newgoals <- premises rules goal;

  --t1 <- stdcrt "a ^ b";
  --t2 <- stdcrt "a ^ (a a)";

  lift2 $ putStrLn "Knowledge Base:";
  lift2 $ sequence [putStrLn $ oTToString fact | fact <- kb];
  lift2 $ putStrLn "Goal:";
  lift2 $ putStrLn $ oTToString goal;
  lift2 $ putStrLn "Actions:";
  actions <- possibleActions [(\u -> (u,t)) <$> (unify t goal >>= applyBindings) | t <- kb];
  lift2 $ sequence [putStrLn $ (show idx) ++ ": " ++ (oTToString o) ++ " from "++(oTToString t) | (idx, ((o,t),_)) <- zip [1..] actions];
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
