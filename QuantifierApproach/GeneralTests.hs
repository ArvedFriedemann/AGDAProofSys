module GeneralTests where

import TestLogic
import Printing
import TermData
import TermFunctions
import FreshenQuantifier
import InferenceRules
import SpecialMatches

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

testkb3 = [            "forall y (append [] y y)",
           "forall (x xs y ys) ( (append xs y ys) -> (append (xs : x) y (ys : x)) )",
                              "length [] zero",
           "forall (x xs i) ( (length xs i) -> (length (xs : x) (suc i)) )"]
testgoal3 = ["append ([] : b : a) ([] : a) x", "length x y"]


testkb4 = [(["A"],["Test A"]),
           (["A"],["Test2 A A"]),
           (["A","B"],["Test2 A B"]),
              ([],["Test bot"])]
testgoal4 = (["A","B","C"],["Test A", "Test B", "Test2 B C"])

testkb5 = ["forall A (Test A)",
           "(forall (A B) (Test A)) -> Test3"]
           --should be: ([],["foall X . Test X", "Test3"])
testgoal5 = ["Test3"]
--TODO! This does not work. There is a difference between (forall a. Test a) -> K and forall a. (Test a -> K). This is the reason universals are needed as terms! Only the top most of them should be evaluated during inference!

testkb5' = ["forall A ((Test A) -> (Test (Test A)))"]
           --should be: ([],["foall X . Test X", "Test3"])
testgoal5' = ["Test A"]

testkb6 = [([],["(P,X) in KB","solve X with KB as P"]),
           ([],["solve (Q -> X) with KB as QX",
                "Q as conjunction list is QL",
                "forall q in QL . solve q with KB as (A q)",
                    "solve X with KB as (QX A1 ... An)"]),
            ([],["KB union {A} is KB'","solve B with KB' as b","solve (A -> B) with KB as (a = b)"])]
testgoal6 = []

freshentest1 = runIntBindQuanT $ do {
  t1 <- stdcrt bounds ["a"] "a b";
  t2 <- freshenUniversal t1;
  oTToStringVP t1 >>= (lift3.putStrLn);
  oTToStringVP t2 >>= (lift3.putStrLn);
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

instantiationtest1 = runIntBindQuanT $ do {
  t1 <- stdcrt bounds [] "forall (X Y) (X Y X)";
  oTToStringVP t1 >>= (lift3.putStrLn);
  instantiateUniversality t1 >>= oTToStringVP >>= (lift3.putStrLn);
}

readrawkbtest1 = runIntBindQuanT $ do {
  stdkb bounds ["forall X (X X X)","forall Y (Y Y)"] >>= readRawKB >>= kbToFormatStringVP >>= (lift3.putStrLn)
}

matchbinappllassoclisttest1 = runIntBindQuanT $ do {
  t1 <- stdcrt bounds [] "a b c d e f";
  oTToStringVP t1 >>= (lift3.putStrLn);
  ts <- matchBinApplLAssocList t1 >>= applyBindingsAll;
  tss <- sequence (oTToStringVP <$> ts);
  lift3 $ putStrLn $ unlines tss;
}
