module UnificationFDKB where

import UnificationFDApproach
import Control.Unification
import Control.Unification.Types
import Control.Unification.IntVar
import Control.Monad.Trans
import Control.Monad.Trans.Except
import Data.Either

type IntKB = ([OpenTerm], [(OpenTerm, OpenTerm)]) --facts and rules

implications :: IntKB -> IntBindMon [OpenTerm]
implications (facts, rules) = allSucceeding [lookout $ applyRule f r | f <- facts, r <- rules]

applyRule :: OpenTerm -> (OpenTerm, OpenTerm) -> IntBindMon OpenTerm
applyRule fact (pre,post) = do {
  lst <- freshenAll [pre,post];
  case lst of
    [pre',post'] -> do {
      unify fact pre';
      applyBindings post'
    }
}

reverseRule :: (OpenTerm, OpenTerm) -> OpenTerm -> IntBindMon OpenTerm
reverseRule (pre,post) fact = do {
  lst <- freshenAll [pre,post];
  case lst of
    [pre',post'] -> do {
      unify fact post';
      applyBindings pre'
    }
}

matchImpl :: OpenTerm -> IntBindMon (OpenTerm, OpenTerm)
matchImpl t = do {v1 <- lift freshVar; v2 <- lift freshVar;
  unify t (list [v1, scon "->", v2]);
  pre <- applyBindings v1;
  post <- applyBindings v2;
  return (pre,post)
}

getImpls :: [OpenTerm] -> IntBindMon [(OpenTerm,OpenTerm)]
getImpls ts = allSucceeding $ (lookout.matchImpl) <$> ts

allSucceeding :: [IntBindMon a] -> IntBindMon [a]
allSucceeding mons = concat <$> (sequence [catchE (return <$> m) (const $ return []) | m <- mons])

splitSucceeding :: (OpenTerm -> IntBindMon a) -> [OpenTerm] -> IntBindMon ([a],[OpenTerm])
splitSucceeding fkt ts = do {
  e <- sequence [catchE (Left <$> fkt t) (const $ return $ Right t) | t <- ts];
  return (lefts e, rights e)
}

stdrd = binds.rt
testrules = map stdrd [("(a = b) -> (b = a)"),("(a ^ b) -> a"), ("(a ^ b) -> b")]
testfacts = map ((bindConst ["k","l"]).stdrd ) ["(k ^ (k k))", "l = k"]

test2 = runIntBind $ do {
  --t <- lift $ freshTermFromString' bounds "a -> (b b)";

  kbr <- sequence $ lift <$> createOpenTerm <$> testrules;
  rules <- getImpls kbr;
  facts <- sequence $ lift <$> createOpenTerm <$> testfacts;
  impls <- implications (facts, rules);
  return $ ppCTerm <$> giveNiceNames <$> fromOpenTerm <$> impls
}

--makeProof':: [OpenTerm] -> [OpenTerm] -> IO ()
--makeProof' kb goals = do {
--
--}
