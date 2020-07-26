module TermApproach where

import Control.Monad.State.Lazy
import Control.Monad.Writer
import Safe
import Data.List


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

conj_list :: [Term p] -> Term p
conj_list [] = CONST TOP
conj_list ls = foldr1 (\x y -> BOP x AND y) ls

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


--TODO! BIIIIIIIIIIG!
--forall x. x=x
impl_eq0 :: VarState p [Term p]
impl_eq0 = do{x <- getVar; return [BIND FORALL x (BOP (VAR x) EQT (VAR x))]}

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
dedc_eq1 (v1@(VAR c1), v2@(VAR c2))
  | c1==c2 = return []
  | otherwise = return [BOP v1 EQT v2]
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
dedc_eq3 (a,c) = do{b <- getVar; return [BIND EXISTS b (BOP (BOP a EQT (VAR b)) AND (BOP (VAR b) EQT c))]}

--Conjunction laws
--A -> B -> A ^ B
impl_conj1 :: (Eq p) => Term p -> Term p -> VarState p [Term p]
impl_conj1 a b = return [BOP a AND b]

dedc_conj1 :: (Eq p) => (Term p, Term p) -> VarState p [Term p]
dedc_conj1 (a,b) = return [a,b]

--A ^ B -> A
impl_conj2 :: (Eq p) => (Term p, Term p) -> VarState p [Term p]
impl_conj2 (a,b) = return [a]

dedc_conj2 :: (Eq p) => Term p -> VarState p [Term p]
dedc_conj2 a = do { b <- getVar; return [BIND EXISTS b (BOP a AND (VAR b))]}

--A ^ B -> B
impl_conj3 :: (Eq p) => (Term p, Term p) -> VarState p [Term p]
impl_conj3 (a,b) = return [b]

dedc_conj3 :: (Eq p) => Term p -> VarState p [Term p]
dedc_conj3 b = do { a <- getVar; return [BIND EXISTS a (BOP (VAR a) AND b)]}



--Disjunction laws
--A -> A v B
impl_disj1 :: (Eq p) => Term p -> VarState p [Term p]
impl_disj1 a = do { b <- getVar; return [BIND EXISTS b (BOP a OR (VAR b))]}

dedc_disj1 :: (Eq p) => (Term p, Term p) -> VarState p [Term p]
dedc_disj1 (a,b) = return [a]

--B -> A v B
impl_disj2 :: (Eq p) => Term p -> VarState p [Term p]
impl_disj2 b = do { a <- getVar; return [BIND EXISTS a (BOP (VAR a) OR b)]}

dedc_disj2 :: (Eq p) => (Term p, Term p) -> VarState p [Term p]
dedc_disj2 (a,b) = return [b]

--A v B, (A -> C), (B -> C) -> C
impl_disj3 :: (Eq p) => (Term p, Term p) ->
                        (Term p, Term p) ->
                        (Term p, Term p) -> VarState p [Term p]
impl_disj3 (a,b) (a',c) (b',c')
  | a==a' && b==b' && c==c' = return [c]
  | otherwise = return []

dedc_disj3 :: (Eq p) => Term p -> VarState p [Term p]
dedc_disj3 c = do { a <- getVar; b <- getVar;
                  return [BIND EXISTS a (BIND EXISTS b (conj_list
                                [BOP (VAR a) OR (VAR b), BOP (VAR a) IMPL c, BOP (VAR b) IMPL c]) )]}



--Implication laws

--A, (A -> B) -> B
impl_impl1 :: (Eq p) => Term p -> (Term p, Term p) -> VarState p [Term p]
impl_impl1 a (a',b)
  | a==a' = return [b]
  | otherwise = return []

dedc_impl1 :: (Eq p) => Term p -> VarState p [Term p]
dedc_impl1 b = do { a <- getVar; return [BIND EXISTS a (BOP (VAR a) IMPL b)]}

--(A -> B), (B -> C) -> (A -> C)
impl_impl2 :: (Eq p) => (Term p, Term p) ->
                        (Term p, Term p) ->
                        VarState p [Term p]
impl_impl2 (a,b) (b',c)
  | b==b' = return [BOP a IMPL c]
  | otherwise = return []

dedc_impl2 :: (Eq p) => (Term p, Term p) -> VarState p [Term p]
dedc_impl2 (a,c) = do { b <- getVar; return [BIND EXISTS b (conj_list [BOP a IMPL (VAR b), BOP (VAR b) IMPL c])]}

--A -> (B -> A)
impl_impl3 :: (Eq p) => Term p -> VarState p [Term p]
impl_impl3 a = do { b <- getVar; return [BIND EXISTS b (BOP (VAR b) IMPL a)]}

dedc_impl3 :: (Eq p) => (Term p, Term p) -> VarState p [Term p]
dedc_impl3 (b,a) = return [a]


--Exchange as rules

--this only assigns when the resulting term t has to be assigned to one of them. So it also has to hold that
--term t <-> t=(CONST c) v t=(VAR x) v t=(a op b) v t=(BIND tp p t)
--t [x | y] to t' -> term t, term t', term x, term y

-- (CONST c) [ x | y ] to (CONST c)
-- (VAR x) [ x | y ] to t <-> t=y
-- (a op b) [ x | y ] to t <-> t=(a' op b'), a [ x | y ] to a', b [ x | y ] to b'
-- (BIND tp x t) [x | y] to (BIND tp x t)
-- (BIND tp p t) [x | y] to t', (p=x -> bot) <-> t [x | y] to t'

--what if one creates the inplications for the matching? Something in the middle?
--So, if there is a fact like forall x. x=x, and we want to prove a=a. then we'd have to prove that is is possible for (x=x)[x\k]=(a=a). The stress is on "possible". So we'd have to prove that (x=x)[x\k]=(a=a) -> top. I guess. in the end, we get that it is possible under the assumption that k=a. how can it be enforced? Actually, only via a disjunction. These premises only become facts when there is no other alternative. Unless there is some exists proof...actually, it should be stated that exists k.(x=x)[x|k]=(a=a). in that case, there could be an actual k, which can be found by forward reasoning. this would work well for hand computation, it is kinda hard for automated deduction. Reason is that the existential variables need to be assigned without being sure that the assignment is neither right nor unique. Quite in fact, in most instances, it is not unique. What can be done though is to prove the possibility of matching by stating that the premises hint towards existance.
--or at least all possible deductions don't prevent it. In that instance it must be provable that bot is not provable.

--QUANTIFIERS!

--forall x. t -> t[x/y]

--t[x] -> forall x. t[x]    iff x is not used anywhere (is this a strong notion?)


--exists is weird...their seems to be a special exists tolen needed to tell whether some arbirarty variable exists or not.
--t[x], exists x -> exists x. t[x]
--x=(a,b), exists a, exists b -> exists x
-- exists x. t[x] -> exists x         needs to be the x created when eliminating the existential








isTop :: Term p -> Bool
isTop (CONST TOP) = True
isTop _ = False

isBot :: Term p -> Bool
isBot (CONST BOT) = True
isBot _ = False

match_op :: BinOp -> Term p -> [(Term p, Term p)]
match_op op (BOP a op' b)
  | op==op' = [(a,b)]
  | otherwise = []
match_op _ _ = []

implications :: (Eq p) => [Term p] -> VarState p [Term p]
implications kb = do {
  eqs <- return $ concatMap (match_op EQT) kb;
  e1 <- sequence $ [impl_eq1, impl_eq2] <*> eqs;
  e2 <- sequence $ impl_eq3 <$> eqs <*> eqs;

  ands <- return $ concatMap (match_op AND) kb;
  c1 <- sequence $ [impl_conj2, impl_conj3] <*> ands;
  c2 <- sequence $ impl_conj1 <$> kb <*> kb;

  ors <- return $ concatMap (match_op OR) kb;
  impls <- return $ concatMap (match_op IMPL) kb;

  d1 <- sequence $ [impl_disj1, impl_disj2] <*> kb;
  d2 <- sequence $ impl_disj3 <$> ors <*> impls <*> impls;

  i1 <- sequence $ impl_impl1 <$> kb <*> impls;
  i2 <- sequence $ impl_impl2 <$> impls <*> impls;
  i3 <- sequence $ impl_impl3 <$> kb;

  return $ concat $ concat [e1,e2,c1,c2,d1,d2,i1,i2,i3]
}

premises :: (Eq p) => Term p-> VarState p [[Term p]]
premises goal = do {
  eqs <- return $ match_op EQT goal;
  e1 <- sequence $ [dedc_eq1, dedc_eq2, dedc_eq3] <*> eqs;

  ands <- return $ match_op AND goal;
  c1 <- sequence $ dedc_conj1 <$> ands;
  c2 <- sequence $ [dedc_conj2, dedc_conj3] <*> [goal];

  ors <- return $ match_op OR goal;
  d1 <- sequence $ [dedc_disj1, dedc_disj2] <*> ors;
  d2 <- sequence $ [dedc_disj3] <*> [goal];

  impls <- return $ match_op IMPL goal;
  i1 <- sequence $ [dedc_impl2, dedc_impl3] <*> impls;
  i2 <- sequence $ [dedc_impl1] <*> [goal];

  return $ {- conj_list  <$> -}(concat [e1,c1,c2,d1,d2,i1,i2])
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
ppterm (BOP t1@(BOP t1a op1 t1b) op t2@(BOP t2a op2 t2b))
    | (oplevel op1) < (oplevel op) &&
      (oplevel op2) < (oplevel op) = tell "(" >> (ppterm t1) >> tell ")" >> ppOp op >> tell "(" >> (ppterm t2) >> tell ")"
    | (oplevel op1) < (oplevel op) = tell "(" >> (ppterm t1) >> tell ")" >> ppOp op >> (ppterm t2)
    | (oplevel op2) < (oplevel op) = ppOp op >> (ppterm t1) >> tell "(" >> (ppterm t2) >> tell ")"
    | otherwise = (ppterm t1) >> ppOp op  >> (ppterm t2)
ppterm (BOP t1@(BOP tt1 op' tt2) op t2)
    | (oplevel op') < (oplevel op) = tell "(" >> (ppterm t1) >> tell ")" >> ppOp op >> ppterm t2
    | otherwise = (ppterm t1) >> ppOp op  >> (ppterm t2)
ppterm (BOP t1 op t2@(BOP tt1 op' tt2))
    | (oplevel op') < (oplevel op) = ppterm t1 >> ppOp op >> tell "(" >> ppterm t2 >> tell ")"
    | otherwise = (ppterm t1) >> ppOp op  >> (ppterm t2)
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
--TODO! existential needs more that just some variable put somewhere. There already needs to be another term! Maybe that should be considered...should pop up when doing the implications reasoning. In that case, the existential one emerges directly from the kb.
goalOriented :: [Term String] -> [Term String] -> [String] -> IO ()
goalOriented kb goals vars = do {
    putStrLn "Goals:";
    putStrLn $ unlines $ ts <$> goals;
    putStrLn "Knowledge Base:";
    putStrLn $ unlines $ ts <$> kb;

    putStrLn "Paths:";
    (newPrems,vars')  <- return $ runState (concat <$> (sequence $ (\g -> (zip $ repeat g) <$> (premises g) ) <$> goals)) vars;
    premsidcs <- return $ [1..(length newPrems)];
    putStrLn $ unlines $ map (\(x, z) -> "("++x++") "++z) $ zip (show <$> premsidcs) ((ts.conj_list.snd) <$> newPrems);

    putStrLn "New Knowledge:";
    (newPosts,vars'') <- return $ runState (implications kb) vars';
    postidcs <- return $ map (+(length newPrems)) [1..(length newPosts)];
    putStrLn $ unlines $ map (\(x, z) -> "("++x++") "++z) $ zip (show <$> postidcs) (ts <$> newPosts);

    idx <- readLn;
    if idx `elem` premsidcs then do {
      (oldGoal, newGoals) <- return $ newPrems !! (idx-1);
      goals' <- return $ filter (not.isTop) ((newGoals ++ goals) \\ [oldGoal]);
      if null (goals' \\ kb)
        then putStrLn "Horray!"
        else goalOriented kb (goals' \\ kb) vars''
    } else if idx `elem` postidcs then do {
      newKnowledge <- return $ newPosts !! ((idx - (length newPrems))-1);
      goalOriented (newKnowledge:kb) goals vars''
    } else do {
      putStrLn "Invalid Index";
      goalOriented kb goals vars --need to be default vars here!
    }


}

--Tests
--goalOriented [BOP (VAR "b") EQT (VAR "a")] [(BOP (VAR "a") EQT (VAR "b"))] defV
--goalOriented [BOP (VAR "b") EQT (VAR "c")] [(BOP (BOP (VAR "a") APPL (VAR "a")) EQT (BOP (VAR "b") APPL (VAR "c")))] defV



--only knowing something has to hold turns goals into knowledge!

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
