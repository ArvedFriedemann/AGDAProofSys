module InferenceRules where

import TermFunctions
import TermData
import FreshenQuantifier
import Control.Unification
import Data.List

type Clause = ([OpenTerm], OpenTerm)
type KB = [Clause]

clauseToList :: Clause -> [OpenTerm]
clauseToList (prems, post) = prems ++ [post]

clauseFromList :: [OpenTerm] -> Clause
clauseFromList lst = (init lst, last lst)

modifyAsList :: (Monad m) => ([OpenTerm] -> m [OpenTerm]) -> Clause -> m Clause
modifyAsList fkt cls = clauseFromList <$> fkt (clauseToList cls)

matchClause :: (Monad m) => Clause -> OpenTerm -> IntBindMonQuanT m Clause
matchClause clause goal = do {
  newclause@(prems, post) <- modifyAsList freshenAllUniversal clause;
  unify post goal;
  checkUniversalsUnbound goal;
  modifyAsList applyBindingsAll newclause; --WARNING: Maybe not needed...but for now, better safe than sorry
}
