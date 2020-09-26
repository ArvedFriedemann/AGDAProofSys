module SpecialMatches where

import TermData
import TermFunctions
import Util
import Printing

import Control.Unification
import Control.Monad.Trans
import Control.Monad.Trans.Except
import Debug.Trace

matchClauseStructure :: (Monad m) => OpenTerm -> IntBindMonQuanT m Clause
matchClauseStructure trm = listToClause <$> (matchBinConstLAssocList IMPL trm)

--gets the content term and the bound (hopefully-)variables.
--does not apply the bindings!
matchUniversalBinding :: (Monad m) => OpenTerm -> IntBindMonQuanT m ([OpenTerm],OpenTerm)
matchUniversalBinding trm = do {
  a <- lift $ freshVar;
  b <- lift $ freshVar;
  ot <- return $ olist [con FORALL, a, b];
  unifySubsumes ot trm;
  hopefullyVars <- matchBinApplLAssocList a;
  b' <- applyBindings b; -- TODO
  return (hopefullyVars, b')
}

applyUniversalCriterion :: (Monad m) => [OpenTerm] -> IntBindMonQuanT m ()
applyUniversalCriterion vars = do {
  sequence (getVar <$> vars);
  checkUniversalsUnbound (olist vars);
}

instantiateUniversality :: (Monad m) => OpenTerm -> IntBindMonQuanT m OpenTerm
instantiateUniversality trm = catchE (lookout $ do {
  (vars,t) <- matchUniversalBinding trm;
  applyUniversalCriterion vars;
  return t
}) (\e -> return trm)

readRawKB :: (Monad m) => RawKB -> IntBindMonQuanT m KB
readRawKB trms = sequence [ do {
  tinst <- instantiateUniversality t;
  matchClauseStructure tinst;
} | t <- trms]
