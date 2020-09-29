module Quoting where

import TermData
import TermFunctions
import Util
import Printing

import Control.Unification
import Control.Unification.IntVar
import Control.Applicative
import Control.Monad.Trans
import Control.Monad.Trans.Except
import Debug.Trace

--returns a term where all variables have been replaced by their id constants. Should be done on applied terms
quoteTerm :: OpenTerm -> OpenTerm
quoteTerm (UVar v) = olist [con NAME, con $ ID v]
quoteTerm (UTerm (CONST c)) = (UTerm (CONST c))
quoteTerm (UTerm (APPL a b)) = UTerm (APPL (quoteTerm a) (quoteTerm b))

quoteTermVP :: (Monad m) => OpenTerm -> IntBindMonQuanT m OpenTerm
quoteTermVP (UVar v) = do {
  vp <- getProperty v;
  return $ olist [con NAME,con $ VP vp, con $ ID v]
}
quoteTermVP (UTerm (CONST c)) = return $ UTerm (CONST c)
quoteTermVP (UTerm (APPL a b)) = do {
  a' <- quoteTermVP a;
  b' <- quoteTermVP b;
  return $ UTerm (APPL a' b')
}

--returns the VarProp and id
matchVPVar :: (Monad m) => OpenTerm -> IntBindMonQuanT m (OpenTerm, OpenTerm)
matchVPVar trm = do {
  a <- lift $ freshVar;
  b <- lift $ freshVar;
  ot <- return $ olist [con NAME, a, b];
  unifySubsumes ot trm;
  return (a,b)
}

matchVPVar' :: (Monad m) => OpenTerm -> IntBindMonQuanT m (VarProp, IntVar)
matchVPVar' trm = do {
  (tp, tid) <- matchVPVar trm;
  tpa <- applyBindings tp;
  tida <- applyBindings tid;
  vp <- (case tpa of
          (UTerm (CONST (VP p))) -> return p
          _ -> throwE (CustomError "not a var prop") );
  iD <- (case tida of
          (UTerm (CONST (ID i))) -> return i
          _ -> throwE (CustomError "not a var id") ) ;
  return (vp, iD)
}

unquoteTermVP :: (Monad m) => OpenTerm -> IntBindMonQuanT m OpenTerm
unquoteTermVP trm = catchE (do {
  (vp,iD) <- matchVPVar' trm;
  setProperty iD vp; --WARNING! This might override existing var properties...
  return (UVar iD)
}) (const $ catchE (do {
  (a,b) <- matchBinAppl trm;
  a' <- applyBindings a >>= unquoteTermVP;
  b' <- applyBindings b >>= unquoteTermVP;
  return $ UTerm (APPL a' b')
}) (const $ return trm))


--WARNING: might want to have a backtrack in case of failure.
applySimpleUnquoting :: (Monad m) => OpenTerm -> IntBindMonQuanT m OpenTerm
applySimpleUnquoting trm = do {
  a <- lift $ freshVar;
  b <- lift $ freshVar;
  ot <- return $ olist [con (UNQUOTE), a, b];
  unifySubsumes ot trm; --TODO: might need extraction...
  (vp,iD) <- applyBindings a >>= matchVPVar'; --just to check whether its a variable
  uq <- applyBindings a >>= unquoteTermVP;
  unify b uq;
}

--applies unquoting goals and only returns goals that didn't unquote.
applySUQGoals :: (Monad m) => [(KB,OpenTerm)] -> IntBindMonQuanT m [(KB,OpenTerm)]
applySUQGoals goals = concat <$> sequence [catchE (tryBM (applySimpleUnquoting g) >> return []) (const $ return [(kb,g)]) | (kb,g) <- goals]


quoteClause :: Clause -> OpenTerm
quoteClause = quoteTerm.clauseToTerm

quoteClauseVP :: (Monad m) => Clause -> IntBindMonQuanT m OpenTerm
quoteClauseVP = quoteTermVP.clauseToTerm

quoteKB :: KB -> OpenTerm
quoteKB = quoteTerm.kbToTerm

quoteKBVP :: (Monad m) => KB -> IntBindMonQuanT m OpenTerm
quoteKBVP = quoteTermVP.kbToTerm
