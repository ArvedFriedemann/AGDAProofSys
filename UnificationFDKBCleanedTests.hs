module UnifikationFDKBCleanedTests where

import UnificationFDKBCleaned
import UnificationFDApproach
import Control.Monad.Trans
import Control.Monad.Trans.Except
import Control.Monad

type StringKB = [[String]]

bounds = ["=","^","->","v","bot", ":","[]", "append", "length", "zero", "suc", "list"]
binds = (bindConstTo [("=",EQT),("->",IMPL)]).(bindConst bounds)
stdrd = binds.rt

stdcrt :: (Monad m) => String -> IntBindMonT m OpenTerm
stdcrt = lift.createOpenTerm.stdrd

stdcrtAll :: (Monad m) => [String] -> IntBindMonT m [OpenTerm]
stdcrtAll trms = lift $ createOpenTerms (stdrd <$> trms)

stdkb :: (Monad m) => StringKB -> IntBindingTT m KB
stdkb stringkb = do {
  sequence $ [listToClause <$> (createOpenTerms (map stdrd clst)) | clst <- stringkb]
}

stdTest :: StringKB -> [String] -> IO (Either MError ())
stdTest strkb goaltrms = runIntBindT $ do {
  goals <- stdcrtAll goaltrms;
  kb <- lift $ stdkb strkb;
  interactiveProof kb goals
}

testkb1 = [["a","a v b"],["b", "a v b"], ["bot", "a"]]
testgoal1 = ["a v b"]

testkb2 = [ ["append [] y y"],
            ["append xs y ys","append (xs : x) y (ys : x)"],
            ["length [] zero"],
            ["length xs i", "length (xs : x) (suc i)"]]
testgoal2 = ["append ([] : b : a) ([] : a) x", "length x y"]

testkb3 = [ ["x = x"],
            ["length [] zero"],
            ["length xs i", "length (xs : x) (suc i)"],
            ["list []"],
            ["list xs", "list (xs : x)"]]
testgoal3 = ["list a", "list b", "a = b"]
