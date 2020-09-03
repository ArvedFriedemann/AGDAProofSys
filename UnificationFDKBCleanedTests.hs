module UnifikationFDKBCleanedTests where

import UnificationFDKBCleaned
import UnificationFDApproach
import Control.Monad.Trans
import Control.Monad.Trans.Except
import Control.Monad

type StringKB = [[String]]

binds = (bindConstTo [("=",EQT),("->",IMPL), ("()", BOT),("bot", BOT)]).(bindConst bounds)
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

bounds = ["=","^","->","v","bot", ":","[]",
          "append", "length", "zero", "suc", "list", "alldiff",
          "1", "2", "3", "4", "5", "6", "7", "8", "9"]

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

--and this is why we need proper negation...or something like it.
testMiniSudokuKB = [["x = x"],
                    ["1 = 2","bot"],
                    ["1 = 3","bot"],
                    ["2 = 1","bot"],
                    ["2 = 3","bot"],
                    ["3 = 1","bot"],
                    ["3 = 2","bot"],
                    ["alldiff ..."]]
                    --TODO: this is a pain in the !@£$ without the ability to derive UNPROOF or implications
