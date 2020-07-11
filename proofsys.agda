module proofsys where

open import util

open import Agda.Primitive
import Relation.Binary.PropositionalEquality as Eq
open Eq using (refl; trans; sym; cong; cong-app; subst) renaming (_≡_ to _===_)

private
  variable
    l : Level


data Term (A : Set) : Set where
  mpt : Term A
  val : A -> Term A
  _appl_ : Term A -> Term A -> Term A

data Formula (A : Set) : Set where
  top : Formula A
  bot : Formula A
  var : A -> Formula A
  _appl_  : Formula A -> Formula A -> Formula A
  _eq_    : Formula A -> Formula A -> Formula A
  _andf_  : Formula A -> Formula A -> Formula A
  _orf_   : Formula A -> Formula A -> Formula A
  _impl_  : Formula A -> Formula A -> Formula A

term-to-form : {A : Set} -> Term A -> Formula A
term-to-form = {! !}

form-to-term : {A : Set} -> Formula A -> Term A
form-to-term = {! !}

--A decidable set is just a function A -> Bool. Things are either in or not.
--would sure be sweet to have some better modification methods, but this'll do.
--would also be nice to be able to convert it to some containter of A, so one could formulate a forall statement.
--There could be set for partial things, which would be a function from (k : K) -> Maybe A. So, if k is an incomplete representation of some A, then the return value would be (all) complete objects fitting at least K. The forall thing would be like K -> Maybe (A -> Bool)

_fkt-union_ : {A : Set} -> (A -> Bool) -> (A -> Bool) -> (A -> Bool)
_fkt-union_ A B = \x -> (A x) || (B x)

_fkt-cut_ : {A : Set} -> (A -> Bool) -> (A -> Bool) -> (A -> Bool)
_fkt-cut_ A B = \x -> (A x) && (B x)

_fkt-neg_ : {A : Set} -> (A -> Bool) -> (A -> Bool)
_fkt-neg_ A = \x -> not (A x)

_fkt-unit_ : {A : Set} -> A -> (A -> Bool)
_fkt-unit_ x elem = x == elem

--The context is the set of terms that each term in a conjunction can use for inference.
context : {A : Set} -> Formula A -> (A -> Bool)
context (A and B) = (context A) fkt-union (context B)
context t = fkt-unit t

--quick brainfart: When deducing next terms, we query the context for certain terms. Technically, every rule could just use the list monad for all combinations of terms (slow but easy to write)
--anyway...context needs to be reversible. Any rule just checks whether unversally quantified premises are in the context and checks whether they are unique

--a term is made of a set of facts. Any checking of the term in the set just asks these facts in the right order.facts are atomic, but carry variables. These are returned after the set query. As facts can depend on these variables (e.g. which concrete address they are), the querying can be recursive.

--query incomplete term by asking for all sets that have a given set (the term) as a subset

-------------------------------------
--
-------------------------------------

--for andorra: get the context. Deductions as queries to the context. All new facts added to the context.
--goal oriented: Quite the same, just with other rules. Better formalism: Only deduce things that make the search faster. Obviously, proceeding to the goal makes things faster. But so does deducing relevant complexity information.
--when only disjunctions left, meta rules have to apply. Do that later, but don't loose track.

--get a set of current facts, returns the set of deducible facts.
deduction-step : {A : Set} -> (Formula A -> Bool) -> (Formula A -> Bool)
deduction-step (_in-ctx) form =  form in-ctx ||
                                  (a in-ctx) && ((a impl form) in-ctx) ||

                                  ((a or b) in-ctx) &&
                                  ((a impl form) in-ctx) &&
                                  ((b impl form) in-ctx) ||

                                  bot in-ctx ||

                                  (form == a impl c) && (a impl b) in-ctx && (b impl c) in ctx ||
                                  ...

provable : {A : Set} -> (Formula A -> Bool) -> Formula A -> Bool
provable ctx form = (deduction-step ctx form) || (provable (deduction-step ctx) form)

eq-prop : {A : Set} -> (Formula A -> Bool) -> (Formula A -> Bool)
eq-prop (_in-ctx) form =  ((a eq b) in-ctx ) ->> exchange a with b in form --something like that

-- TODO: universal rules
--this is not andorra yet. This is just backtrack proving stuff...just a little smarter maybe. The idea of andorra is that facts are just being deduced. Like code completion. Maybe it is when having several goals? All incomplete code becomes a goal? All time information becomes a goal? When having several goals, try all of them and the first one wins? There should maybe be goal reduction rules for when too much happens at the same time...Or finding out the next goal then is the new single goal.
--That's it! When having a disjunction, the new goal is to dissolve the disjunction! Now, fewer rules hold and the disjunction ID does not give new facts.


--this is also not andorra yet because this just does depth first search again. In fact, everz query should give a new context. When a goal is queried, it could be unknown whether it is in. Querying another goal could give that knowledge though.

--technically, there could also be a function mapping a term to its proof obligations, but when descending them down always carrying a context of things with it. open goals are queued until all other goals are done with it.

--for free variables...maybe disjunct the possibilities? Or just ask whether something holds universally? Nope...universality does not imply existance. What if some P -> (A -> C) and (C -> B) holds...then only P needs to be proven. So under some contexts, variables hold universaly.
prove ctx (A and B) = add A >>= add B >>= prove A >>= prove B
prove ctx (A impl B) = prove (A impl C) >>= prove (C impl B)
prove ctx (A or B) = stop
prove ctx form = if form in ctx then goals remove form else nothing

--goal oriented reasoning just puts the goals also into the context and reasons them until disjunction. A disjunction stays a passive goal that can only be resolved by other facts

prove ctx form = form in ctx || prove' (ctx + form) form

prove ctx [] = bot in ctx
prove ctx goals = prove new-ctx new-goals --Get rid of goals in ctx. get new goals of each goal. Add them to ctx. Make them be new goals.
  where act-goals = goals \\ ctx
        new-goals = map (step ctx) act-goals
        new-ctx =  ctx ++ new-goals

-- problem: the possible premises can only be derived when all implications are known. If there are implications missing it doesn't work. Should be captured by disjunction elimination...
--main problem with just implementing it straight forward is the existential quantification. is it though? It resolves deterministaicallz...

--goals just as a fact (goal t). If that fact is up and unproven, only things that prove the fact can be deduced.
--(exists x a b c d. x=(a b), b=(c d), c=eq) -> a = d


--bruteforce. Take two facts and combine them to something new. Only combine them when outcome is interesting. More general...only combine them when there is reason to.


{-
general idea: deterministic machine running on a set of facts. This set is interconnected, machine runs on connections. Relevant facts always reach machine eventually.
Set contains facts and transformations of facts. Given a goal it finds the path from initial facts to goal. In case of nondeterminism, facts on the correct way needed. facts on own working also included

facts as general traversable graph, where traversal behaves such that facts in and out don't break. Facts that go in can always be retrieved again and facts that go out are always consequences of facts coming in.

Build a proper Set in AGDA! (or find out how it's done...)

Do the andorra in AGDA or whatnot


solve dilemma between two andorra principles

-}
