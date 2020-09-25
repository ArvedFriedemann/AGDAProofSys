module SpecialMatches where

import TermData
import TermFunctions

matchClauseStructure :: (Monad m) => OpenTerm -> IntBindMonQuanT m Clause
matchClauseStructure trm = listToClause <$> (matchBinConstLAssocList IMPL trm)
