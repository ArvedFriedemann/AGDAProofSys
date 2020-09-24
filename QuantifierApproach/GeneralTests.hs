module GeneralTests where

import TestLogic
import Printing
import TermData
import TermFunctions
import FreshenQuantifier
import InferenceRules

import Control.Unification
import Control.Monad.Trans

bounds = ["=","->","^","v","bot",":","[]",
          "Test", "Test2", "Test3",
          "append", "length", "zero", "suc", "list", "consteq",
          "subject", "predicate","object", "the", "car", "person", "carries", "sentence","moth", "question", "alldiff", "permut", "member_rem", "sudoku",
          "1","2","3","4","5","6","7","8","9"]

stdTest = stdTest' bounds

testkb1 = [(["a","b"],["a","a v b"]),
           (["a","b"],["b", "a v b"]),
           (["a"],["bot", "a"])]
testgoal1 = ([],["a v b"]) --as we want actual assignments for a and b, they are not universal

testkb2 = []
testgoal2 = ([],["bot -> a"]) --as we want actual assignments for a, it is not universal

testkb3 = [           (["y"],["append [] y y"]),
            (["xs","y","ys"],["append xs y ys","append (xs : x) y (ys : x)"]),
                         ([],["length [] zero"]),
             (["xs","i","x"],["length xs i", "length (xs : x) (suc i)"])]
testgoal3 = ([],["append ([] : b : a) ([] : a) x", "length x y"])


testkb4 = [(["A"],["Test A"]),
           (["A"],["Test2 A A"]),
           (["A","B"],["Test2 A B"]),
              ([],["Test bot"])]
testgoal4 = (["A","B","C"],["Test A", "Test B", "Test2 B C"])

freshentest1 = runIntBindQuanT $ do {
  t1 <- stdcrt bounds ["a"] "a b";
  t2 <- freshenUniversal t1;
  lift3 $ putStrLn $ oTToString t1;
  lift3 $ putStrLn $ oTToString t2;
}

unificationtest1 = runIntBindQuanT $ do {
  t1 <- stdcrt bounds [] "a b";
  t2 <- stdcrt bounds [] "c d";
  (_, post) <- matchClause ([],t1) t2;
  --lift3 $ putStrLn $ "Alive";

  lift3 $ putStrLn $ oTToString t1;
  lift3 $ putStrLn $ oTToString t2;
  lift3 $ putStrLn $ oTToString post;
}
