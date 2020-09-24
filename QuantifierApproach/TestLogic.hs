module TestLogic where

import TermData
import TermFunctions
import Interaction
import Printing

import Data.List
import Data.Map as Map
import Data.Set as Set
import Control.Monad
import Control.Monad.Trans

type StringKB = [([String],[String])] --every clause needs to carry its universal variables

binds = \bounds -> (bindConstTo $ Map.fromList [("/=",NEQ),("=",EQT),("->",IMPL),("^",CONJ),("v",DISJ), ("()", BOT),("bot", BOT)]).(bindConst bounds)
stdrd = \bounds -> (binds bounds).rt

stdVarProp :: (Ord a) => [a] -> a -> VarProp
stdVarProp lst v = if Set.member v (Set.fromList lst)
                   then UNIVERSAL
                   else NEUTRAL


stdcrt :: (Monad m) => [String] -> [String] -> String -> IntBindMonQuanT m OpenTerm
stdcrt bounds universals = (createOpenTerm $ stdVarProp universals).(stdrd bounds)

stdcrtAll :: (Monad m) => [String] -> [String] ->  [String] -> IntBindMonQuanT m [OpenTerm]
stdcrtAll bounds universals trms = createOpenTerms (stdVarProp universals) ((stdrd bounds) <$> trms)

stdkb :: (Monad m) => [String] -> StringKB -> IntBindMonQuanT m KB
stdkb bounds stringkb = do {
  sequence $ [listToClause <$> (createOpenTerms (stdVarProp univ) ((stdrd bounds) <$> clst)) | (univ, clst) <- stringkb]
}

stdTest' :: [String] -> StringKB -> ([String],[String]) -> IO (Either MError ())
stdTest' bounds strkb (goaluniv, goaltrms) = runIntBindQuanT $ do {
  goals <- stdcrtAll bounds goaluniv goaltrms;
  kb <- stdkb bounds strkb;
  interactiveProof [(kb, g) | g <- goals]
}
