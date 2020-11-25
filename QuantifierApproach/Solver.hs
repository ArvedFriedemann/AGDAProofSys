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
          "choose", "recurseProofs", "check","concat",
          "c0","c1","c2","c3","c4","c5","c6","c7","c8","c9",
          "t0","t1","t2","t3","t4","t5","t6","t7","t8","t9",
          "cA","cB","cC","cD","cE","cF","cG","cH","cI","cJ"]

stdTest = stdTest' False bounds
stdTestUniv = stdTest' True bounds
stdTestUnivBounds b = stdTest' True (bounds ++ b)

--TODO: this does not yet allow for splits nor termination check
--TODO: refreshing of types
checkkb = [
  --"X = X",
  "(choose mergeop X X)",
  "(choose mergeop X (XS mergeop X))",
  "(choose mergeop X XS) -> (choose mergeop X (XS mergeop Y))",
  "(concat (id mergeop) id Y Y)",
  "(concat (id mergeop) XS Y Z) -> (concat (id mergeop) (XS mergeop X) Y (Z mergeop X))",

  "(recurseProofs prems (x : T) init init)",
  "(check (p : (prems => (newprf : P)) )) -> " ++
  "(recurseProofs prems (x : P) init (init newprf))",
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
  "(check (p : (P => (prf : G)) ))",
  --just choose a fact. No recursion needed.
  "(choose => (ak : G) P ) -> " ++
  "(check (p : (P => (ak : G)) ))",
  --have the premises of the to be proven implication be actual premises.
  "(concat ((h0 : T) =>) prems P P') -> "++
  "(check (p : (P' => (prf : G))) ) -> "++
  "(check (p : (P => (prf : (prems => G)))) )"--This is new
  ]
checkgoal0 = ["check (c0 : ((c3 : cA) => (prf : cA)) )"]
checkgoal1 = ["check (c0 : ((c4 : ((c3 : cA) => (c5 : cB)) ) => (c1 : cA) => (prf : cB) ) )"]


implgoal0 = ["check (c2 : ((t1 : T) => (c3 : ((t2 : T) => (c5 : cA) => (c6 : cB))) => (c0 : ((t0 : T) => (c1 : cA) => (prf : cB))) ))"]



{-
A split can be performed on things with rules like
(avb : A v B) -> (pl : A -> C) -> (pr : B -> C) -> (split ((left a) = pl) ((right b) = pr) : C)
More arbitrarily:
(k : K) -> (p1 : P1 -> C) -> ... -> (pn : Pn -> C) -> (prf : C)
If this holds, to proof ((k : K) -> C), there can be several lines where k is exchanged by the constructors p1 ... pn, together with a split constructor. In order to have this be executable, there needs to be another function
(avb : A v B) -> (left a : A) v (right b : B)
that can extract which of the constructors created the proof. This could technically be done with the concrete proofs, as in this case there should only be
(left a : A v B) and (right b : A v B)
Problem here is ensuring this to be always possible. If there are several different ways to create the same type it is no longer sure that this splitting can always occur (there would need to be a transformation).
There can be a statement stating:
((left : A -> A v B) ^ (left a : A v B)) v ((right : B -> A v B) ^ (right b : A v B))
(avb : A v B) -> (left a : A v B) v (right b : A v B)
maybe with a more designated disjunction. This would be a data declaration. A split could then be just all disjunctive parts put into the proof.

Generally speaking we get the same proof line, but with exchanged proof variables. So there is not one but a list of proof outcomes. So
(avb : A v B) -> (split avb p1 p2 : A v B)
where the split is possible iff there is a disjunction present, like
(left : (a : A) -> (left a : A v B)) v (right : (b : B) -> (right b : A v B))
This however only states that these are two possibilities. It does not state that if both are proven, it holds forall avb : A v B. This would allow for several possible definitions of avb. While this is fine for proofs, it is hard to transform into a program.
With the disjunction elimination rule that would be a bit easier. Then, one needs to have at least the rule that disjunctions elimination works and a program could rely on it. In this setting, the proof procedure would stay the same, and there wouldn't even be a switching of variables (old proof still available). For this, there would only need to be the possibility to prove implications by adding their premises (which I think was already done). Therefore, only the specific disjunction elim rule needs to be part of the premises and everything is ok.
splitv : (avb : A v B) -> (left : (a : A) -> (p1 : C)) -> (right : (b : B) -> (p2 : C)) -> (splitv avb p1 p2 : C)
For nicer output, these splits would need to be translated into new proof lines, which would need to reference the context in which the rule was applied. The rule itself does not tell how avb is supposed to look like, but its realisor would need to choose an interface to avb that allows for this distinction.

Side note: This makes termination checking easy. Never allow the recursion to be used in the proof directly, but just give it as an input to the downward recursion. Within the splits already it is valid to use. However, it needs to be made sure that one of the arguments from the split is being used. Therefore, the recursion could be optionally given if it is applied to the splitted agrument.
-}

splitgoal0bounds = ["p","splitv","left","right","cac","cbc"]
splitgoal0 = [
  "check (p : ((t0 : T) => (avb : (cA v cB)) => " ++
  "(splitv : ((t1 : T) => (avb' : A v B) => (left : ((t2 : T) => (a : A) => (p1 : C)) ) => (right : ((t2 : T) => (b : B) => (p2 : C)) ) => ((splitv avb' p1 p2) : C)) ) => " ++
  "(cac : ((t3 : T) => (a' : cA) => (c2 : cC))) => " ++
  "(cbc : ((t3 : T) => (b' : cB) => (c4 : cC))) => " ++
  "(prf : cC) ))"
  ]

{-
Issues: first of all, the whole function instantiation thing does not work well yet. Second: it is not yet sure whether implications can be properly proven. When the goal is an implication, it should work, but I never tried.
Generally: Whenever one goes into the proof recursion, the proof variables of the applied rule should be refreshed.
-}


{-
Theory of splitting due to disjunction elimination rule
(A v B) -> (A -> C) -> (B -> C) -> C
In AGDA done with data declarations. In this model, something different is needed like
(left : (a : A) -> (pl : C)) -> (right : (b : B) -> (pr : C)) -> (split (left a = pl) (right b = pr) : C)
This proof can be done without premises. If for all possible premises it holds its a proof. Whats still needed is the possibility to proof implications by assuming the premises in the KB.
-}

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
