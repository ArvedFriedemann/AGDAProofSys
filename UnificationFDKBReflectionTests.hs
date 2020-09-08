module UnificationFDKBReflectionTests where

import UnificationFDKBCleaned
import UnificationFDApproach
import Control.Monad.Trans
import Control.Monad.Trans.Except
import Control.Monad

type StringKB = [[String]]

binds = (bindConstTo [("/=",NEQ),("=",EQT),("->",IMPL),("^",CONJ),("v",DISJ), ("()", BOT),("bot", BOT), ("top", TOP)]).(bindConst bounds)
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

bounds = ["=","->","^","v","bot",":","[]",
          "append", "length", "zero", "suc",
          "solve", "deduce", "from", "with", "in", "as","conjunction", "is",
          "improvable", "because"]

reflTestKB = [["x = x"],
              ["x in x"],
              ["x in a","x in (a ^ b)"],
              ["x in b","x in (a ^ b)"],
              ["A as conjunction is A"], --TODO: this base case doesn't work!
              ["A as conjunction is A'","(A -> B) as conjunction is (A' ^ B)"],
              ["goal in kb","deduce goal from kb with proof"],
              ["deduce (A -> goal) from kb with ag",
                "A as conjunction is implconj",             --NOTE: feels weird to have the ^ inbetween
                "deduce implconj from kb with conj",
                  "deduce goal from kb with (ag conj)"],
              ["A as conjunction is implconj",
                "deduce goal from (kb ^ implconj) with proof",
                  "deduce (A -> goal) from kb with proof"]     --TODO: Is the proof thing correct?
              --[]
            ]

reflTestGoal = ["kb = (A ^ (A -> B))",
                "deduce B from kb with proof"]
{-
Congratulations! All goals fulfilled!
Initial Goals:
z3 ^ (z3 -> z4) = (z3 ^ (z3 -> z4))
deduce z4 from (z3 ^ (z3 -> z4)) with (c9 d2)
-}

--TODO: Maybe make a special Goal IMPROV that is fulfilled when there are no steps left
reflTestKB2 = [["x = x"],
                ["(A in kb) improvable from kb because p'",
                  "((B -> A) deducible from kb with pba) ->
                      (B as conjunction is implconj) ->
                      (implconj improvable form kb because pprem)",
                  "A improvable from kb because p"],
                ["A improvable from kb because pa",
                  "B improvable from kb because pb",
                    "(A v B) improvable from kb because p"],
                ["A improvable from kb because pa",
                    "(A ^ B) improvable from kb because p"],
                ["B improvable from kb because pa",
                    "(A ^ B) improvable from kb because p"],

              --[]
            ]

reflTestGoal2 = ["kb = (A ^ (A -> B))",
                "deduce B from kb with proof"]
