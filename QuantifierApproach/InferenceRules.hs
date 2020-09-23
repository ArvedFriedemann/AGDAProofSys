module InferenceRules where

import Util
import TermFunctions
import TermData
import FreshenQuantifier
import Control.Unification
import Data.List



matchClause :: (Monad m) => Clause -> OpenTerm -> IntBindMonQuanT m Clause
matchClause clause goal = do {
  newclause@(prems, post) <- modifyAsList freshenAllUniversal clause;
  unify post goal;
  checkUniversalsUnbound goal;
  applyClause newclause; --WARNING: Maybe not needed...but for now, better safe than sorry
}

backwardPossibilities :: (Monad m) => KB -> OpenTerm -> IntBindMonQuanT m [(Clause, IntBindMonQuanT m Clause)]
backwardPossibilities kb goal = possibleActions [matchClause c goal | c <- kb]

backwardPossibilitiesClause :: (Monad m) => KB -> Clause -> IntBindMonQuanT m [(Clause, IntBindMonQuanT m Clause)]
backwardPossibilitiesClause kb (prems, post) = possibleActions [matchClause c post | c <- kb']
  where kb' = (return <$> prems) ++ kb
