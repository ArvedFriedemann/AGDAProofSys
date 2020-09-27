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

bounds = ["=","->","^","v","bot",":","[]"]

stdTest = stdTest' bounds

testkb = [
  --natural deduction
  "forall (a b) (a -> (a v b))",
  "forall (a b) (b -> (a v b))",
  "forall (a b c) ((a v b) -> (a -> c) -> (b -> c) -> c)",

  "forall (a b) (a -> b -> (a ^ b))",
  "forall (a b) ((a ^ b) -> a)",
  "forall (a b) ((a ^ b) -> b)",

  "forall a (bot -> a)",
  --equality and substitution
  "forall x (x = x)",
  "forall (A B C) ( (B = C) -> ((A B) = (A C)) )",
  "forall (A B C) ( (B = C) -> ((B A) = (C A)) )",
  --equivalence
  "forall (A B) ((A -> B) -> (B -> A) -> (A <-> B))",
  --ite
  "forall (A B C) ( (A -> B) -> (ite A then B else C) )",
  "forall (A B C) ( ((A -> bot) -> C) -> (ite A then B else C) )",
  --typing rules
  "forall (f a A B) ( (f : (A -> B)) -> (a : A) -> ((f a) : B) )",
  "forall (x A) ( (x : A) -> A )",
  --my take on an existential quantifier...
  "forall (x A) ( A -> (exists x A) )",
  "forall (x A) ( (exists x A) -> (x : A) )",

  "forall f ((deterministic f) <-> (forall (a b) ((a = b) -> (f a) = (f b) ) )) ",

  --TODO: function evaluation
  "(executeStep f with [] into x) -> bot",
  "ite ( lst = (xs : (f = a)) )" ++
  "then (executeStep f with lst into a)" ++
  "else (executeStep f with xs into x)",
  "(executeStep f with lst into x) -> (executeRec f with lst in implctx into x)",
  "(executeStep f with lst into a) -> "++
  "   (lst' implements a in implctx) -> "++
  "   (executeRec a with lst' in implctx into x) -> "++
  "   (executeRec f with lst  in implctx into x)",

  "solve : Solver", --explicitly no forall! This thing should be unique!
  "solve goal on kb with proof"
  --if the solver is modeled as a function that always has to be specifically executed this becomes kinda cumbersome. Maybe determinism criterion should be enough, combined with some lookahead? Important thing is just that the KB can change...

]
testgoal = ["a v b"]


--TODO: remove possibilities if they (immediately) imply falsity
