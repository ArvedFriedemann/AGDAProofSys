module UnifikationFDKBCleanedTests where

import Control.Unification
import UnificationFDKBCleaned
import UnificationFDApproach
import UnificationFDTestLogic
import Control.Monad.Trans
import Control.Monad.Trans.Except
import Control.Monad


bounds = ["=","->","^","v","bot",":","[]",
          "append", "length", "zero", "suc", "list", "consteq",
          "subject", "predicate","object", "the", "car", "person", "carries", "sentence","moth", "question", "alldiff", "permut", "member_rem", "sudoku",
          "1","2","3","4","5","6","7","8","9"]
          
stdTest = stdTest' bounds

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


testkblang = [["subject (the car)"],
              ["subject (the moth)"],
              ["object (the person)"],
              ["predicate (carries)"],
              ["subject A","predicate B", "object C","sentence (A B C)"],
              ["subject B","predicate A", "object C","question (A B C)"]]
testlanggoal = ["question (X Y Z)"]

testkbsudoku = [["x = x"],
                ["member_rem A (AS : A) AS"],
                ["member_rem A XS XS'","member_rem A (XS : X) (XS' : X)"],
                ["permut [] []"],
                ["member_rem x ys ys'","permut ys' xs","permut ys (xs : x)"],
                ["p = ([] : 1 : 2 : 3 : 4 : 5 : 6 : 7 : 8 : 9)",
                  "permut p ([] : x11 : x12 : x13)",
                  "permut p ([] : x21 : x22 : x23)",
                  "permut p ([] : x31 : x32 : x33)",
                  "permut p ([] : x11 : x21 : x31)",
                  "permut p ([] : x12 : x22 : x32)",
                  "permut p ([] : x13 : x23 : x33)",
                  "permut p ([] : x11 : x12 : x13 : x21 : x22 : x23 : x31 : x32 : x33)",
                  "sudoku (x11 x12 x13 x21 x22 x23 x31 x32 x33)"]]
testsudokugoal = ["sudoku (x11 x12 x13 x21 x22 x23 x31 x32 x33)"]

testkbsudokusmall = [["x = x"],
                      ["member_rem A (AS : A) AS"],
                      ["member_rem A XS XS'","member_rem A (XS : X) (XS' : X)"],
                      ["permut [] []"],
                      ["member_rem x ys ys'","permut ys' xs","permut ys (xs : x)"],
                      ["p = ([] : 1 : 2)",
                        "permut p ([] : x11 : x12)",
                        "permut p ([] : x21 : x22)",
                        "permut p ([] : x11 : x21)",
                        "permut p ([] : x21 : x22)",
                        "sudoku (x11 x12 x21 x22)"]]
testsudokugoalsmall = ["sudoku (x11 x12 x21 x22)"]


--easy solution: propagate equalities in KBs. Valid eqs vanish, invalid ones deduce bot.
--or...to avoid propagation...just have special behaviour when bot is active...so that possibilities suddenly are failing facts...as of now these are onlz failing equalities.
--put that into the backwards possibilities...
--any kind of implication then solved with KB modification.

--this is an example of how a finer equality can be achieved. With the consteq predicate, a more primitive form of equality allows for derivations of bot. Only problem with this approach is that the consteq predicate is best created on the fly...
testIneqKB = [["constant true"],
              ["constant false"],
              ["constant ="], --and so on..should be done on the fly...
              ["constant (a b)", "bot"], --this holds because a constant is never a compound
              --general idea of equality
              ["A = C", "B = D","(A B) = (C D)"], --generally important rule...
              ["constant A","constant B", "consteq A B", "A = B"],
              --rule for consteq
              ["consteq y x","consteq x y"], --this holds to ease writing
              ["consteq true false", "bot"], --and so on and so forth.
              ["consteq true =", "bot"],
              []] -- ...
--WARNING: (consteq x y) -> bot can only be used for backward reasoning iff there is a finite number of constants. in other cases, prolly new constants would need to be allowed creating...
testIneqGoal = ["(true = false) -> bot"]
<<<<<<< HEAD


testImplKB = [["x = x"],["x = x"],
              ["bot", "x"],
              ["bot", "x"]]
testImplGoal = ["(A = bot) -> (F bot) -> (F A)", "A = top"]
--this does not work. If the binding is applied to A, it traverses outside. But maybe that's ok...if the proof is done in a way that does not fit the overall rules it should not have been possible...
--I should try with giving a possibility to derive bot properly...

--this breaks currently for several reasons: first, there is no distinction between existential and universal variables, so everything unassigned is just treated universal which makes rule application weird. Second, I haven't quite figured out in the backwardsPossibilities function what would be the returned clause...there is something odd there...

testImplKB2 = []
testImplGoal2 = ["A -> (A -> B) -> B"]
--TODO: Have existential and universal variables! Not gonna work otherwise!
=======
>>>>>>> b502f85f0ffabb4eebc3ced525ddadfd6e3f699b
