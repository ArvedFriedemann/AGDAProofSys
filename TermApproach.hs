module TermApproach where

import Control.Monad.State.Lazy
import Control.Monad.Writer
import Safe


data Constant = TOP | BOT deriving (Show, Eq)
data BinOp = AND | OR | IMPL | EQT | APPL deriving (Show, Eq)
data BindType = EXISTS | FORALL deriving (Show, Eq)
data Term p =   CONST Constant
              | VAR p
              | BOP (Term p) BinOp (Term p)
              | BIND BindType p (Term p) deriving (Show, Eq)

type VarState p = State [p]
type KB p = [Term p]

getVar :: VarState p p
getVar = do {
  s <- get;
  case s of
    (x:xs) -> put xs >> return x
    [] -> error "no more variables"
}

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






exchangeVar :: (Eq p) => p -> p -> Term p -> Term p
exchangeVar _ _ c@(CONST k) = c
exchangeVar x y (VAR x')
    | x==x' = VAR y
    | otherwise = VAR x'
exchangeVar x y (BOP a op b) = BOP (exchangeVar x y a) op (exchangeVar x y b)
exchangeVar x y (BIND tp p t)
    | p == x = BIND tp p t
    | otherwise = BIND tp p (exchangeVar x y t)


--These two are almost identical!
--implications and proof obligations for a=b
impl_eq1 :: (Eq p) => (Term p, Term p) -> VarState p [Term p]
impl_eq1 (CONST c1, CONST c2)
    | c1==c2 = return []
    | otherwise = return [CONST BOT]
impl_eq1 (VAR _, VAR _) = return []
impl_eq1 (BOP a op b, BOP a' op' b')
    | op==op' = return [BOP a EQT a', BOP b EQT b']
    | otherwise = return [CONST BOT]
impl_eq1 (BIND tp p t, BIND tp' p' t')
    | tp == tp' = do {v <- getVar; return [BOP (exchangeVar p v t) EQT (exchangeVar p' v t')]}
    | otherwise = return [CONST BOT]

dedc_eq1 :: (Eq p) => (Term p, Term p) -> VarState p [Term p]
dedc_eq1 (CONST c1, CONST c2)
    | c1==c2 = return []
    | otherwise = return [CONST BOT]
dedc_eq1 (v1@(VAR _), v2@(VAR _)) = return [BOP v1 EQT v2]
dedc_eq1 (BOP a op b, BOP a' op' b')
    | op==op' = return [BOP a EQT a', BOP b EQT b']
    | otherwise = return [CONST BOT]
dedc_eq1 (BIND tp p t, BIND tp' p' t')
    | tp == tp' = do {v <- getVar; return [BOP (exchangeVar p v t) EQT (exchangeVar p' v t')]}
    | otherwise = return [CONST BOT]

--symmetry a=b -> b=a
impl_eq2 :: (Eq p) => (Term p, Term p) -> VarState p [Term p]
impl_eq2 (a, b) = return [BOP b EQT a]

dedc_eq2 :: (Eq p) => (Term p, Term p) -> VarState p [Term p]
dedc_eq2 (a, b) = return [BOP b EQT a]

--transitivity a=b b=c -> a=c
impl_eq3 :: (Eq p) => (Term p, Term p) -> (Term p, Term p) -> VarState p [Term p]
impl_eq3 (a,b) (b',c)
   | b==b' = return [BOP a EQT c]
   | otherwise = return []

dedc_eq3 :: (Eq p) => (Term p, Term p) -> VarState p [Term p]
dedc_eq3 (a,c) = do{b <- getVar; return [BOP a EQT (VAR b), BOP (VAR b) EQT c]}

from_equivalence :: Term p -> [(Term p, Term p)]
from_equivalence (BOP a EQT b) = [(a,b)]
from_equivalence _ = []

implications :: (Eq p) => [Term p] -> VarState p [Term p]
implications kb = do {
  eqs <- return $ concatMap from_equivalence kb;
  p1 <- sequence $ [impl_eq1, impl_eq2] <*> eqs;
  p2 <- sequence $ impl_eq3 <$> eqs <*> eqs;
  return $ concat $ p1 ++ p2
}

premises :: (Eq p) => Term p-> VarState p [Term p]
premises goal = do {
  eqs <- return $ from_equivalence goal;
  p <- sequence $ [dedc_eq1, dedc_eq2, dedc_eq3] <*> eqs;
  return $ conj_list1 <$> p
}

--some pretty printing

oplevellist = [OR, AND, IMPL, EQT, APPL]
oplevel :: BinOp -> Int
oplevel op = elemIndexJust op oplevellist

ts :: Term String -> String
ts t = execWriter (ppterm t)

ppterm :: Term String -> Writer String ()
ppterm (CONST TOP) = tell "T"
ppterm (CONST BOT) = tell "()"
ppterm (VAR v) = tell v
ppterm (BOP t1@(BOP tt1 op' tt2) op t2)
    | (oplevel op') < (oplevel op) = tell "(" >> (ppterm t1) >> tell ")" >> ppOp op >> (ppterm t2)
    | otherwise = (ppterm t1) >> ppOp op  >> (ppterm t2)
ppterm (BOP t1@(BIND tp p t) op t2) = tell "(" >> (ppterm t1) >> tell ")" >> ppOp op  >> (ppterm t2)
ppterm (BOP t1 op t2) = (ppterm t1) >> ppOp op  >> (ppterm t2)
ppterm (BIND FORALL p t) = tell ("forall "++p++".") >> (ppterm t)
ppterm (BIND EXISTS p t) = tell ("exists "++p++".") >> (ppterm t)

ppOp :: BinOp -> Writer String ()
ppOp OR = tell "v"
ppOp AND = tell "^"
ppOp IMPL = tell "->"
ppOp EQT = tell "="
ppOp APPL = tell " "

defV = map ("x"++) $ show <$> [1..]

goalOriented :: [Term String] -> Term String -> [String] -> IO ()
goalOriented kb goal vars = do {
    putStrLn "Knowledge Base:";
    putStrLn $ unlines $ ts <$> kb;
    putStrLn "Paths:";
    (newPrems,vars') <- return $ runState (premises goal) vars;
    putStrLn $ unlines $ ts <$> newPrems
}



--quantifiers now done with kinda like functions. rules are
--forall x t[x] -> t[x/y] -- so a term either just holds or it has a variable that can be swallowed by a universal quantifier.
--t[x] -> forall x t[x] --and here is where the binding somehow comes into place
--for real application, equality has to somehow come into place. So, if a fact holds, it is either already in the kb, or it is equal to an existing term. For this equality, assignments have to be possible. So, a term can hold if it can be extracted from a universal quantifier with assignable variables which are then equal to the term. so:
--(forall x t), t[x/y]=p -> p      where y is existentially bound
--note how this is a two step thing. So technically we generally have
--a,a=p->p
--this only results in an automated algorithm if at some point the usage of a rule is enforced, probably through some law of excluded middle. Only then will assignments pop up top level.

--this will mainly be used in a hypothetical setting. "If this term matches...", so mainly as a goal.
--probably variables need to always be universally bound. If we do the reasoning with the facts "forall x. A[x]" and "forall y. B[y] -> C[y]" then it holds that "forall z. C[z]" for C[z] being the greatest common unifier of A[x] and B[y] with bindings applied to C[y].

--essentially, universal introduction only works if there is no assignment on some variable x. As long as there isn't, it's universal. As soon as there is however, it can only be existential. What's weird is if it is unknown whether the variable will have an assignment or not. The case in point is, if there is a fact P -> x=10, and we want to make some A[x] universal, we can't, unless we know that P is unprovable. What we can however always infer is that we take some term with a variable, and derive the universal statement as an implication. So in this case, it would be forall x. x=10 -> A[x]. Same for the other way around, So actually forall x. x=10 <-> A[x]. Just using the x=10 is a bit too strong though. We can derive the universal statement by using the whole clause as a premise. So, for this example, forall x. (P -> x=10) -> A[x]. Or, in general, forall x. B[x] -> A[x], where B[x] are all terms that use x conjuncted.

--when using universal rules for matching, in the premise, it should be checked whether the terms already match. Technically, this premise whould only ask for some of the variables equality. lets say, we want to match the term (k a b) with the universal (k x x), where x is universally bound, which here means its top level with a fresh variable. So we have the rule (k x x) -> P, and somewhere the fact that a=b. The rule would now need to be in the form (t, t=(k,t'), t'=(y,z), y=z) -> P. There are a lot of existential variables in there. In the implication rule, one would ask a, a=b, b->c -> c. If it is solid where the a is applied, and it is known that a and b are equal, then the rule applied. Lucky hit if that happens during forward reasoning, but backward reasoning becomes interesting. for that one, euqlity of the posterior has to be established. Assume it is, then all premises become facts and...welll...this is weird...we constantly need equality, but kinda have to compute it first.
--Also...just checking whethter two terms are equal will, for differing variable always end in the conditions that the unknown variables stay the same. Wait...if unit propagation is applied, equal variables  will always eventually be the same pointer. Only the what-if cases remain hard. Problem with universal ones is that here, for the universal variables, any equality should follow, as they are arbitrary...kinda. That doesn't mix well with them being existentially somewhere. While that makes non matching easy to detect, it leads to an inconsistency when done top level.
--Problem is that probably all variables are universally bound, so it's a common unificator problem, and that unificator might introduce new premises. So, for bare universal thigns, no assignments can be made and only new premises are introduced wich have to be removed later -.-
--The reason PROLOG does this unification automatically is because it forces to take a certain way, along which it just assigns everything that's necessary.
--when making a universal statement out of many less universal ones, this is where greated common unificator would come in handy. Create all greatest common ones and then hold them on top of each other to get rid of the variable. So we wanna prove forall x. (P x) and have P a,P b,P c and x=a v x=b v x=c -> P x. This works. Prove forall x. (P x) by putting it somewhere with a fresh variable, like (P y). This says nothing on how to prove it, unless x=y. With this assumption, the thing is easily proven. Somehow though, we cannot get rid of it. For that, we need to universally bind the long rule. if the x in the long rule is universally bound, any equality should be valid. Does that make sense? adding an equality for universal stuff whould always be possible, but onlz in instantiation.

--when trying to show that a term results from an instantiation, just do bruteforce term matching. like
--(forall x. t), t[x/y], y=z -> t[x/z]
--that way the equalities stay in the premise. this should follow from the other rules...


--t[x] -> exists x t[x] -- so if a term exists find one
--exists x t[x] -> t[x], ((exists x x) v (x=(a,b))) -- so if a term exists it has to have a new variable that has to exist

--they are both nuts in one direction. Maybe fewer rules or something? Or avoid the nuts direction? I mean...it's not like its going anywhere and bidrectional search should do the trick...
