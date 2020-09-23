module UnificationFDTestLogic where

import UnificationFDKBCleaned
import UnificationFDApproach
import Control.Monad.Trans
import Control.Monad.Trans.Except
import Control.Monad


type StringKB = [[String]]

binds = \bounds -> (bindConstTo [("/=",NEQ),("=",EQT),("->",IMPL),("^",CONJ),("v",DISJ), ("()", BOT),("bot", BOT)]).(bindConst bounds)
stdrd = \bounds -> (binds bounds).rt

stdcrt :: (Monad m) =>[String] -> String -> IntBindMonT m OpenTerm
stdcrt bounds = lift.createOpenTerm.(stdrd bounds)

stdcrtAll :: (Monad m) => [String] ->  [String] -> IntBindMonT m [OpenTerm]
stdcrtAll bounds trms = lift $ createOpenTerms ((stdrd bounds) <$> trms)

stdkb :: (Monad m) => [String] -> StringKB -> IntBindingTT m KB
stdkb bounds stringkb = do {
  sequence $ [listToClause <$> (createOpenTerms (map (stdrd bounds) clst)) | clst <- stringkb]
}

stdTest' :: [String] -> StringKB -> [String] -> IO (Either MError ())
stdTest' bounds strkb goaltrms = runIntBindT $ do {
  goals <- stdcrtAll bounds goaltrms;
  kb <- lift $ stdkb bounds strkb;
  interactiveProof kb goals
}
