module GeneralTests where

import TestLogic
import Printing
import TermData
import TermFunctions
import FreshenQuantifier
import InferenceRules
import SpecialMatches
import Quoting

import Control.Unification
import Control.Monad.Trans

bounds = ["=","->","^","v","bot",":","[]",
          "Test", "Test2", "Test3",
          "cA", "cB", "cC", "cD",
          "append", "length", "zero", "suc", "list", "consteq",
          "in","contains","all",
          "subject", "predicate","object", "the", "car", "person", "carries", "sentence","moth", "question", "alldiff", "permut", "member_rem", "sudoku",
          "1","2","3","4","5","6","7","8","9"]

stdTest = stdTest' bounds

testkb1 = ["forall (a b) (a -> (a v b))",
           "forall (a b) (b -> (a v b))",
           "forall a (bot -> a)"]
testgoal1 = ["a v b"] --as we want actual assignments for a and b, they are not universal

testkb2 = []
testgoal2 = ["bot -> a"] --as we want actual assignments for a, it is not universal

testkb3 = [            "forall y (append [] y y)",
           "forall (x xs y ys) ( (append xs y ys) -> (append (xs : x) y (ys : x)) )",
                              "length [] zero",
           "forall (x xs i) ( (length xs i) -> (length (xs : x) (suc i)) )"]
testgoal3 = ["append ([] : b : a) ([] : a) x", "length x y"]


testkb5 = ["forall A (Test A)",
           "Test Test"]
testgoal5 = ["forall A (Test A)"]

testkb5' = ["forall A ((Test A) -> (Test (Test A)))"]
testgoal5' = ["Test A"]

testkb6 = [([],["(P,X) in KB","solve X with KB as P"]),
           ([],["solve (Q -> X) with KB as QX",
                "Q as conjunction list is QL",
                "forall q in QL . solve q with KB as (A q)",
                    "solve X with KB as (QX A1 ... An)"]),
            ([],["KB union {A} is KB'","solve B with KB' as b","solve (A -> B) with KB as (a = b)"])]
testgoal6 = []

--TODO: This is where the solving KB is explicitly needed!
--also NOTE: I found out how goals can be encoded as implications and that the next state goals can just be added as normal goals, which just need to be lazily unquoted...that might be some huge convenience


--this should traverse in just one meta step
testkb7 = ["forall (a b) (a -> (a v b))",
           "forall (a b) (b -> (a v b))",
           "cA",
           "forall (a b a' b' a'' b'' c d p1 p2) (solve ( ((name forall a) -> ((name forall a) v (name forall b))) -> "++
                    --c as a placeholder for the solvingterm itself
                    "((name forall b') -> ((name forall a') v (name forall b'))) -> c -> d -> "++
                    "((name p1 a'') v (name p2 b''))" ++
           ") (cA) )"]
testgoal7 = ["a v b"]

--this should traverse in just one meta step
testkb8 = ["forall (a b) (a -> (a v b))",
           "forall (a b) (b -> (a v b))",
           "cA",
           "x = x",
           "forall (a b a' b' a'' b'' c d e p1 p2) (solve ( ((name forall a) -> ((name forall a) v (name forall b))) -> "++
                    --c as a placeholder for the solvingterm itself
                    "((name forall b') -> ((name forall a') v (name forall b'))) -> c -> d -> e -> "++
                    "((name p1 a'') v (name p2 b''))" ++
           ") ((name p1 a'') = cA) )"]
testgoal8 = ["a v b"]



--TODO: fix inline unquoting maybe?

testkb7 = [
            "append [] x x",
            "(append xs y zs) -> append (xs : x) y (zs : x)",

            "[] contains all T",
            "((x = (a ^ b)) -> bot) -> (([] : x) contains all x)",
            "(as contains all a) -> (bs contains all b) -> (append as bs z) -> (z contains all (a ^ b))"]
testgoal7 = ["z contains all (cA ^ (cB ^ cC))"]



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

matchbinconstlassoclisttest1 = runIntBindQuanT $ do {
  t1 <- stdcrt bounds [] "a -> b -> c -> d -> e -> f";
  oTToStringVP t1 >>= (lift3.putStrLn);
  ts <- matchBinConstLAssocList IMPL t1 >>= applyBindingsAll;
  tss <- sequence (oTToStringVP <$> ts);
  lift3 $ putStrLn $ unlines tss;
}

quotetest1 = runIntBindQuanT $ do {
  kb <- stdkb bounds ["forall X (X = X)","forall (op X) ((refl op) -> (X op X))"] >>= readRawKB;
  qkb <- quoteKBVP kb;
  lift3 $ putStrLn $ oTToString $ qkb;
  uqkb <- unquoteTermVP qkb;
  oTToStringVP uqkb >>= (lift3.putStrLn);
}

quotetest2 = runIntBindQuanT $ do {
  goal <- stdcrt bounds ["X"] "X";
  target <- stdcrt bounds [] "X";
  qg <- quoteTermVP goal >>= applyBindings;
  quoteGoal <- return $ olist [con UNQUOTE, qg, target];
  lift3 $ putStrLn $ oTToString $ qg;
  lift3 $ putStrLn $ oTToString $ goal;
  lift3 $ putStrLn $ oTToString $ quoteGoal;
  uquq <- applySUQGoals [([],quoteGoal)];
  (lift3.putStrLn) $ show $ length uquq;
  applyBindings quoteGoal >>= oTToStringVP >>= (lift3.putStrLn);
  applyBindings goal >>= oTToStringVP >>= (lift3.putStrLn);
}
