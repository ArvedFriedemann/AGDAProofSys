module NewInference where

import TermData
import TermFunctions
import SpecialMatches


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
