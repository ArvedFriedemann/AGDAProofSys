module TermApproach where

import Control.Monad.State.Lazy

data BinOp = AND | OR | IMPL deriving (Show, Eq)
data BindType = EXISTS | FORALL deriving (Show, Eq)
data Term p =   TOP
              | BOT
              | VAR p
              | APPL (Term p) (Term p)
              | EQ (Term p) (Term p)
              | BOP (Term p) BinOp (Term p)
              | BIND BindType p (Term p) deriving (Show, Eq)

type VarState p = State [p]
type KB p = [Term p]

conj_list1 :: [Term p] -> Term p
conj_list1 = foldr1 (\x y -> BOP x AND y)

disj_list1 :: [Term p] -> Term p
disj_list1 = foldr1 (\x y -> BOP x AND y)

--get first premise and the rest as posterior
match_impl :: (Eq p) => Term p -> [(Term p, Term p)]
match_impl (BOP a IMPL b) = [(a,b)]
match_impl _ = []

--get all premises and the posterior
split_impl :: (Eq p) => Term p -> [([Term p], Term p)]
split_impl (BOP a IMPL b) = case split_impl b of
                              [(prems, post)] -> [(a:prems, post)]
                              [] -> [([a],b)]
split_impl _ = []

implications :: (Eq p) => KB p -> [Term p]
implications kb = [b | a <- kb, (a',b) <- concatMap match_impl kb, a==a']

--warning! Needs to be disjuncted!
premises :: (Eq p) => Term p -> KB p -> [Term p]
premises goal kb = [conj_list1 prems | (prems,b) <- concatMap split_impl kb, b==goal]


--quantifiers now done with kinda like functions. rules are
--forall x t[x] -> t[x/y] -- so a term either just holds or it has a variable that can be swallowed by a universal quantifier.
--t[x] -> forall x t[x] --and here is where the binding somehow comes into place

--t[x] -> exists x t[x] -- so if a term exists find one
--exists x t[x] -> t[x], ((exists x x) v (x=(a,b))) -- so if a term exists it has to have a new variable that has to exist

--they are both nuts in one direction. Maybe fewer rules or something? Or avoid the nuts direction? I mean...it's not like its going anywhere and bidrectional search should do the trick...
