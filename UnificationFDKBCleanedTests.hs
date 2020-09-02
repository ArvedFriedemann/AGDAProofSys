module UnifikationFDKBCleanedTests where

import UnificationFDKBCleaned
import UnificationFDApproach
import Control.Monad.Trans
import Control.Monad.Trans.Except
import Control.Monad

type StringKB = [[String]]

bounds = ["=","^","->","v","bot"]
binds = bindConst bounds
stdrd = binds.rt

stdcrt :: (Monad m) => String -> IntBindMonT m OpenTerm
stdcrt = lift.createOpenTerm.stdrd

stdkb :: (Monad m) => StringKB -> IntBindingTT m KB
stdkb stringkb = do {
  sequence $ [listToClause <$> (createOpenTerms (map stdrd clst)) | clst <- stringkb]
}

stdTest :: StringKB -> String -> IO (Either MError ())
stdTest strkb goaltrm = runIntBindT $ do {
  goal <- stdcrt goaltrm;
  kb <- lift $ stdkb strkb;
  void $ interactiveProof' kb [goal]
}

testkb1 = [["a","a v b"],["b", "a v b"], ["bot", "a"]]
testgoal1 = "a v b"
