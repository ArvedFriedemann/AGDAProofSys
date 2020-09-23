module GeneralTests where

import TestLogic
import Printing
import TermData
import TermFunctions
import FreshenQuantifier
import Control.Unification

bounds = ["=","->","^","v","bot",":","[]",
          "append", "length", "zero", "suc", "list", "consteq",
          "subject", "predicate","object", "the", "car", "person", "carries", "sentence","moth", "question", "alldiff", "permut", "member_rem", "sudoku",
          "1","2","3","4","5","6","7","8","9"]

stdTest = stdTest' bounds

testkb1 = [["a","a v b"],["b", "a v b"], ["bot", "a"]]
testgoal1 = ["a v b"]


freshentest1 = runIntBindQuanT $ do {
  t1 <- stdcrt bounds "a b";
  --TODO...something needs to be set to universal...
  t2 <- freshenUniversal t1;
  lift3 $ putStrLn $ oTToString t1;
  lift3 $ putStrLn $ oTToString t2;
}
