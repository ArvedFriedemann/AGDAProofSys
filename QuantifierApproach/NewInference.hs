module NewInference where

import TermData
import TermFunctions
import SpecialMatches

nextGoals :: KB -> Clause -> OpenTerm -> IntBindMonQuanT m [(KB, OpenTerm)]
nextGoals kb (prems, post) goal = do {
  unify post goal;
  return [(kb, pre) | pre <- prems]
}

--problem: while only one goal is observed, all goals need to be propagated once a choice is made
propagateDepth :: Int -> [(KB,OpenTerm)] -> IntBindMonQuanT m [(KB, OpenTerm)]
propagateDepth 0 goals = return goals
propagateDepth n goals = concat <$> (sequence $ [do {
  possibs <- allSucceeding [nextGoals kb cls goal | cls <- kb]
  case possibs of
    [] -> throwE (CustomError "No proof possibilities left")
    [(_,action)] -> action
    disj -> [action >>= propagateDepth (n-1) | action <-(snd <$> disj)]
} | (kb, goal) <- goals]}

{-
propagateDepth :: Int -> KB -> OpenTerm -> IntBindMonQuanT m [(KB, OpenTerm)]
propagateDepth 0 kb goal = return [(kb, goal)]
propagateDepth n kb goal = do {
  possibs <- allSucceeding [nextGoals kb cls goal | cls <- kb]
  case possibs of
    [] -> throwE (CustomError "No proof possibilities left")
    [(_,action)] -> action
    disj -> allSucceeding
}
-}

{-
probably plain andorra thing needed. All branches spread out until one goal turns deterministic. This branch is then applied to the memory and all other branches are reevaluated.
-}

{-
Every call to solve should be a DTM, starting at an assignment and walking through it. Occasionally, the path it takes depends on its run on the current assignment. However, this is not really the current, but more any assignment really.

actually, it has a current state and does not know what choice to make. Now it searches for a general rule on how to proceed. This can be assignment specific, but does not have to be.
When proving implications, it's like asking whether the thing is solvable on a different initial state. Parallel machine is started on a minimal definition of the state. This might branch again. If it does, additional assignments on the original state have to be propagated. Problem is: To model this, assignment needs to be explicit.

solve asm prop goal prf succ asm'

(solve asm A G prfA succA asmA') ->
(solve asm B G prfB succB asmB') ->
(choose [(left prfA,succA,asmA'), (left prfB,succB,asmB')]
        (prf,true,asm')) ->
(solve asm (A v B) G prf succ asm')

(solve asm A G prfA succA asmA') ->
(solve asm B G prfB succB asmB') ->
(asm' = asmA') ->
(asm' = asmB') ->
(solve asm (A ^ B) G prf succ asm')

The assignment should be a steadily growing object. However, there has to be the possibility to model the question for whether an error occurred. in this case, after simulating the error, the assignment needs to be made smaller again (backtracking), which cannot happen. Therefore, the assignment needs to be copied for asking potential questions. Sometimes however, that assignment needs to be remerged with the original assignment though. This is where proofs come into action. Applying a proof to an assignment should change the assignment the same way as it did in the original assignment.
-}

{-
solve asm prop goal proof success
--problem is the assignment changes with the proof. If the same assignment is referenced for the proof alternatives, it gets changed with them, which should only be the case if they succeed. So the branches should run on an isomorphic assignment that can be unified with the original one. This copying process could be made lazy in case the original assignment changes. Problem is that in that case, barely anything would change because it cannot be determined whether the assignment will ever change. Therefore, there have to be deductions made based on the current knowledge.

assignments from unification cannot be made if it is unclear whether the unification should also be done in the original assignment. as this cannot be determined, it needs to be tried out using a split, which it can't as the split algorithm has not been completed.

What if every algorithm just runs on its own assignment and pushes generally usable statements to the outside, whcih other algorithms can use again.

General architecture: Don't just share the assignment of a value. Share the constraint put on that value. An assignment is just a set of those constraints.

assignments need to be copied, proof needs to be produced, and proof is applied to original assignment. If the original assignment changed in the meantime, proofs need to be reevaluated. But it needs to be done on difference assignments, and each assignment needs to know what its origin was so that it can update.
-}

{-
several programs, that run on different memory, but with shared variables. Problem: Their initial state is not known. It should be the initial assignment, which can change by some branches gatting information. As initial assignment can only grow, it could be modeled as a data stream that all branches are attached to, but that they can only communicate back to under some circumstances (like the assignment becomes unique).
This could also be modeled by saying that when branching occurs, not all variables are exchanged (in fact, should be only those that are branched upon). Problem: What happens if such a variable gets assigned in a branch that does not necessarily have to succeed? In this case, variables would need copying, but then results don't traverse properly anymore. Therefore, one-sided stream structure needed. Original assignment can push new assignments into the branches. This new knowledge is then immediately propagated. A less general version of this can be modeled by keeping the branches with their initial memory and reevaluating them when that memory changes. This can flip a branch from succeeding to failing, meaning that its success value is a genuine different value. Therefore, the old idea of just putting the branches onto a stack for evaluation does not really work...they need to constantly be updated with their origin memory and their proofs need to be redone.
-}

{-
same rules, but with better quoting mechanism (all constructors have names, everything is a list etc.)

(append [] X X)
(append XS Y ZS) -> (append (XS :: X) Y (ZS :: X))

(mapOaa op [] [])
(op L L') -> (mapOaa LS LS') -> (mapOaa op (LS :: L) (LS' :: L'))

(fstOp op (A op B) A)
(sndOp op (A op B) B)

(mapOaa (fstOp :) prems prfs) ->
(append prfs ([] :: p) premsprf) -> --q p1 ... pn = prf
()
(solve (p : (impl (prems :: Q)) ) Q (premsprf = prf) success)

-}

{-
use same mechanic as before, but allow for sharing variables between branches?
-}

{-
(solve (q1' : A1) Q (q1prf = sth1) succeeds1) ->
... ->
(solve (qn' : An) Q (qnprf = sthn) succeedsn) ->
(solve (q' : Q) Q (qnpprf = qkprf) succeedsq) -> --TODO: termination
(choose [q1prf,...,qnpprf] qkprf) ->   --TODO: give the whole state
(success = succeedsk) ->
(solve (q : (q1 : A1) -> ... -> (qn : An) -> Q) Q (q q1'... qn' = qkprf) success)
-}

{-
--TODO: IMPORTANT! WARNING! When having the disjunctive goals as parallel goals as well, DO NOT propagate by first fit first. That would result in a depth first search. Here, a proper scheduler is needed!

(solve Ak G prf) -> (solve (A1 v ... v An) G k).
(solve A1 G prf1) ->
... ->
(solve An G prfn) ->
  (solve (A1 ^ ... ^ An) G (pfr1 ... prfn)).
(solve (A1 ^ ... ^ An) G prf) -> (solve (A1 -> ... -> An -> G) G prf).

--disjunctive case when doing everything at once:
(solve A1 G prf1) ->
... ->
(solve An G prfn) ->
(exactlyOne [prf1, ..., prfn] prfk) ->
(solve (A1 v ... v An) G k)

--generalised for better choosing:
(solve A1 G prf1) ->
... ->
(solve An G prfn) ->
(choose [prf1, ..., prfn] prfk) ->
(solve (A1 v ... v An) G k)
-}

{-
(proof ((p1 : P11 -> ... -> P1n1) ->
      ... -> (pn : Pn1 -> ... -> Pnnn) -> (pk1 : Pk1)) PEX) ->
... ->
(proof ((p1 : P11 -> ... -> P1n1) ->
      ... -> (pn : Pn1 -> ... -> Pnnn) -> (pkn : Pkn(k-1))) PEX) ->
(Q = Pknk) ->
(pq = ([] :: pk :: pk1 :: ... :: pkn)) ->
(proof (pq : (p1 : P11 -> ... -> P1n1) ->
      ... -> (pn : Pn1 -> ... -> Pnnn) -> Q) PEX) --all proofs need to exist

--all possibilities are operated at the same time as well, but disjuncted.
(proof (p1 : P) ex1)
...
(proof (pn : P) exn)
(proof (porig : P) exorig)
(oneof ([] :: ex1 :: ... :: exn))
(exactlyOne ([] :: ex1 :: ... :: exn) exk) -> (porig = pk)
--all of these operated simultaneously, but they don't have to succeed.
-}



--When having a KB and a goal to prove, directly split it into all possible paths. Link the paths together with the proof objects. Apply the proof object to the original problem once unique.
--solve goal proof --the predicate for the proof, where proof is kind of a maybe value (for nothing if there is no proof)
--((solve P1 P) v ... v (solve Pn P)) -> (solve (P1 -> ... -> Pn -> goal) P)
--This is then split such that variables are reinstantiated, but some pointer to the original variable is maintained. As soon as only one branch is left, the pointers are retransferred. The other direction though still transferes the information backwards (so if P is deduced, the information should travel into all branches.)
--functionally, this could be implemented by keeping the monad for every branch. These are then in a broad search manner executed, permanently applying a branch once it is the only one of its competitors.
--outlook: It should be possible to deduce the order in which the statements are checked for memory conservation. Only if that order is not fix branching can occur.






--TODO write solver KB that does splitting
{- solver notes

--((P' = (proof P)) v (P' = (no-proof P))) -> (solve input P')

(solve P1 p1) -> ... -> (solve Pn pn) ->
(PRF typecheck with {p1,...,pn}) ->
  (solve (P1 -> ... -> Pn -> Q) PRF)

--when having an unresolvable disjunction, the predicate can be split
--this needs the ability to have disjunct goals!!!
--disjunct goals are created by splitting the terms and memory they operate on. As the proof object however stays the same regardness of memory, it can be shared between the split versions. Therefore, a disjunct goal does not have to be fulfilled, but it can be used to talk about all possible solutions. If exactly one proof succeeds in the disjunction, it is the proof that is being applied to the main memory.
((solve A P1) v (solve B P2)) -> (P1 = (proof P)) ->
  (solve (A v B) P)
((solve A P1) v (solve B P2)) ->
(P1 = (no-Proof X)) -> (P2 = (proof P))
  (solve (A v B) P)

--to really implement this, probably an explicit proof term is needed...
-}
