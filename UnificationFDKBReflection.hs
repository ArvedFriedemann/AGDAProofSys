module UnificationFDKBReflection where

import UnificationFDKBCleaned


clauseToTerm :: (Monad m) => Clause -> IntBindMonT m OpenTerm
clauseToTerm cls = olist $ intersperse (con IMPL) (clauseToList cls)

kbToTerm :: (Monad m) => KB -> IntBindMonT m OpenTerm
kbToTerm kb = olist $ intersperse (con CONJ) (clauseToTerm <$> kb)
