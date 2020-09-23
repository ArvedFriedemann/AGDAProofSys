module TestLogic where

import TermData
import TermFunctions
import Interaction
import Printing

import Data.List
import Data.Map as Map
import Control.Monad
import Control.Monad.Trans

type StringKB = [[String]]

binds = \bounds -> (bindConstTo $ Map.fromList [("/=",NEQ),("=",EQT),("->",IMPL),("^",CONJ),("v",DISJ), ("()", BOT),("bot", BOT)]).(bindConst bounds)
stdrd = \bounds -> (binds bounds).rt

stdcrt :: (Monad m) =>[String] -> String -> IntBindMonQuanT m OpenTerm
stdcrt bounds = lift.createOpenTerm.(stdrd bounds)

stdcrtAll :: (Monad m) => [String] ->  [String] -> IntBindMonQuanT m [OpenTerm]
stdcrtAll bounds trms = lift $ createOpenTerms ((stdrd bounds) <$> trms)

stdkb :: (Monad m) => [String] -> StringKB -> IntBindingTT m KB
stdkb bounds stringkb = do {
  sequence $ [listToClause <$> (createOpenTerms ((stdrd bounds) <$> clst)) | clst <- stringkb]
}

stdTest' :: [String] -> StringKB -> [String] -> IO (Either MError ())
stdTest' bounds strkb goaltrms = runIntBindQuanT $ do {
  goals <- stdcrtAll bounds goaltrms;
  kb <- lift $ stdkb bounds strkb;
  interactiveProof [(kb, g) | g <- goals]
}
