module InferenceRules where

import Util
import TermFunctions
import TermData
import FreshenQuantifier
import Control.Unification
import Data.List
import Debug.Trace



matchClause :: (Monad m) => Clause -> OpenTerm -> IntBindMonQuanT m Clause
matchClause clause goal = do {
  newclause@(prems, post) <- modifyAsList freshenAllUniversal clause;--freshenAll clause; --
  unify post goal;
  --checkUniversalsUnbound goal; --TODO !!!!!!!!!!
  applyClause newclause; --WARNING: Maybe not needed...but for now, better safe than sorry
}

backwardPossibilities :: (Monad m) => KB -> OpenTerm -> IntBindMonQuanT m [(Clause, IntBindMonQuanT m Clause)]
backwardPossibilities kb goal = possibleActions [matchClause c goal | c <- kb]

backwardPossibilitiesClause :: (Monad m) => KB -> Clause -> IntBindMonQuanT m [(Clause, IntBindMonQuanT m Clause)]
backwardPossibilitiesClause kb (prems, post) = backwardPossibilities ((return <$> prems) ++ kb) post
