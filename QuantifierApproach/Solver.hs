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

bounds = ["=","->","^","v","bot",":","::","[]","=>","true","false",
          "choose", "recurseProofs", "check",
          "c0","c1","c2","c3","c4","c5","c6","c7","c8","c9",
          "t0","t1","t2","t3","t4","t5","t6","t7","t8","t9"]

stdTest = stdTest' False bounds
stdTestUniv = stdTest' True bounds

--TODO: this does not yet allow for splits nor termination check
--TODO: refreshing of types
testkb = [
  --"X = X",
  "(choose mergeop X (XS mergeop X))",
  "(choose mergeop X XS) -> (choose mergeop X (XS mergeop Y))",

  "(recurseProofs prems (true : T) init init)",
  "(recurseProofs prems PS init prf) -> " ++
  "(check (p : (prems => (newprf : P)) )) -> " ++ --TODO: if this recurses, some with clause is needed!
  "(recurseProofs prems (PS => (oldp : P)) init (prf newprf))",

  "check (A : T)", --Anything proofs true (no universe polymorphism)
  --Include the recursion into the premises
  --"(PREM = (P => (p : (P => (prf : G)) )) ) -> "++
  --"(PREM = P ) -> "++
  --choose from the premises together with the recursive call
  "(choose => (ak : (P' => (h1 : G)) ) P ) -> " ++
  "(recurseProofs P P' ak prf) -> "++
  "(check (p : (P => (prf : G)) ))"
  ]
testgoal0 = ["check (c0 : ((A : T) => (c1 : ((h1 : T) => (c3 : A))) => (prf : A)) )"]
testgoal1 = ["check (c0 : ((t2 : T) => (c4 : ((h1 : T) => (c3 : t1) => (c5 : t2) )) => (c1 : ((h1 : T) => (c6 : t1))) => (prf : t2)) )"]



{-
Tasks:
proof checker predicate
  just checks a proof. Turns deterministic once proof and proposition are fix.
solving predicate on quoted terms
  just a general solving predicate, constrained such that it outputs a proof of a quoted term
solving predicate for state change
  a predicate used in the solving process that modeles the states the system goes through. Might be related to the general solving predicate. The general predicate is called on its own state recursively.
propagation predicate
  a predicate to model the propagation behaviour of a formula. This needs to be tied to the actual propagation mechanism and needs to be strong enough to express deterministic computation.
complexity proofs
  Make sure the path taken is reasonable about ressources. This should further determinise the proof search! (when there are several proofs, take the fastest one. When there are several fastest, take a random one (or make propositions, whatever is best))
-}

{-
solve kb G k p success
(read as: Maybe k : (a1 : A1) -> ... -> (an : An) -> (p : G) ,
with (ai : Ai) in kb)

(solve ([ak : Ak1 -> ... -> Akn -> G,ak1 : Ak1,...,akn : Akn] subseteq [k : ... ,a1 : A1,...,an : An]) true) -> --this works with quoting methods...warning about assignment consistency
(solve (k : (a1 : A1) -> ... -> (an : An) -> (ak ak1 ... akn : G)) success)

where kb is just the set of premises (ai : Ai)
which should just be some set (solve kbi gi pi si)
the proof is the path taken through the kb
-}



--IDEA: The next KB and goals need to be deduced as well. so every time there is a decision, the state still having decisions is quoted and deducing the next of it is placed as a goal too, and then further evaluated. the next state stays incomplete, but can be further propagated if possible. It might be that this changes the order of deductions, but that should be fine as the result is always the same modulo isomorphism. fact is, that each state is quoted, put as a goal and deduced further, and the next state is its unquoted version (where possible). This can be modeled by letting the unquote afloat if impossible, just putting a variable where there ought to be a value. Therefore, unquoting can just be a special predicate, as it would only work on a fully instantiated value anyway.

--First, deductions are made on the lowest level. Then, if there are no more deductions left, they can be done one the quoted level. And on the quoted level of the quoted level, until no more deductions are possible.

--in the end, proof is not interactive anymore. One adds universal rules until the proof succeeds. It is still shown where the proof stops without continuation.

--Technically this should be linear. So, from the goals with KBs attached, compute the next goals (with kbs attached). There has to be at least one goal computed. A new goal can only be in the next state if the reason existed in the previous one. inbetween, arbitrary computation can be performed, but rules on the solving itself have to be followed. The solver is always part of the goals. currently, goals have an own KB each, sharing only through variables. the solver needs an own KB that can be altered.

--solve ownkb goal nextgoal
--ownkb contains solveq -> quote (solve smkb g ng) solveq -> solve smkb g ng
--[(ownkb, solve 'ownkb 'goal 'nextgoal)] where ' means quote, is kinda what's aimed for, which means that goal contains the solver goal again and so on.
