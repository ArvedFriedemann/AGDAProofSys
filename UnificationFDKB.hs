module UnificationFDKB where

import UnificationFDApproach
import Control.Unification
import Control.Unification.Types
import Control.Unification.IntVar
import Control.Monad.Trans
import Control.Monad.Trans.Except

type IntKB = ([OpenTerm], [(OpenTerm, OpenTerm)]) --facts and rules

implications :: IntKB -> IntBindMon [OpenTerm]
implications (facts, rules) = concat <$> sequence [catchE (return <$> (lookout $ applyRule f r)) (const $ return []) | f <- facts, r <- rules]

applyRule :: OpenTerm -> (OpenTerm, OpenTerm) -> IntBindMon OpenTerm
applyRule fact (pre,post) = do {
  lst <- freshenAll [pre,post];
  case lst of
    [pre',post'] -> do {
      unify fact pre';
      applyBindings post'
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
getImpls ts = concat <$> (sequence $ [catchE (return <$> matchImpl t) (const $ return []) | t <- ts])

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
