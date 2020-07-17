module AtomicApproach where

data Term p = VAR p | APPL p p

eq (EQ a b) (EQ b (c,d)) = --check if in kb
eq (EQ a b) (EQ a (c,d)) = --check if in kb
eq (EQ a b) (EQ a (c,d)) (EQ b (c',d')) = ()
eq (EQ a b) = --check if in kb, or (EQ a c) (EQ c b)

impl (VAR p) (IMPL a b) (EQ p a) = (VAR p)

...

data SolveState a = {vars::[a],
                      eqs::[(Term p,Term p)],
                      impls::[(Term p,Term p)]}

--deduction rules as functions.
--impl is the direction of "If I know something, what do I know next"
--dedc is the direction of "If I want to know something, what do I need to know first"
--for dedc direction, if a thing still needs proof but nothing is available, it stays as still in need of proof.
--every rule assumes that first it was checked whether a fact is already in the kb.

-- a=a -> top
impl_eq1 :: (Eq a) => Term a -> Term a -> [Term a]
impl_eq1 _ _ =  []
dedc_eq1 :: (Eq a) => Term a -> Term a -> [Term a]
dedc_eq1 (VAR p1) (VAR p2)
  | p1 == p2 = []
  | otherwise = [EQ p1 p2]
dedc_eq1 _ _ = [EQ p1 p2]

--this should be moved to an extra term section...
--dedc_eq1 (APPL a b) (APPL a' b') = [EQ a a', EQ b b']
--dedc_eq1 _ _ = [] --TODO: this is not quite right...if a constant should be equal to a tuple that should give bot...

-- a=b -> b=a
impl_eq2 :: (Eq a) => Term a -> Term a -> [Term a]
impl_eq2 a b =  [EQ b a]
dedc_eq2 :: (Eq a) => Term a -> Term a -> [Term a]
dedc_eq2 a b =  [EQ b a]
-- a=b b=c -> a=c
impl_eq3 :: (Eq a) => (Term a,Term a) -> (Term a,Term a) -> [Term a]
impl_eq3 (a,b) (b',c)
  | b==b' = [EQ a c]
  | otherwise = []
dedc_eq3 :: (Eq a) => Term a -> Term a -> [Term a]
dedc_eq3 a b = [EQ p1 k, EQ k p2] --TODO: that k needs to be existential!


--term stuff------------------------

-- (a,b)=(c,d) -> a=c, b=d
impl_eq4 :: (Eq a) => Term a -> Term a -> [Term a]
impl_eq4 (APPL a b) (APPL c d) =  [EQ a c, EQ b d]
impl_eq4 _ _ =  []
dedc_eq4 :: (Eq a) => (Term a,Term a) -> (Term a,Term a) -> [Term a]
dedc_eq4 (a,c) (b,d) =  [EQ (APPL a b) (APPL c d)] --TODO: This might need some fancy data structure.


--TODO: exchange axioms. So a=b,t -> t[a/b]. Could be done by directly applying a=b to everything...

--logical connectives------------------------

--b->(a->b)
impl_implication1 :: (Eq a) => Term a -> [Term a]
impl_implication1 b = [IMPL a b]--TODO: existential
dedc_implication1 :: (Eq a) => (Term a, Term a) -> [Term a]
dedc_implication1 (a,b) = [b]

-- a,(a->b) -> b
impl_implication2 :: (Eq a) => Term a -> (Term a,Term a) -> [Term a]
impl_implication2 a (a',b)
  | a == a' = [b]
  | otherwise = []
dedc_implication2 :: (Eq a) => Term a -> [Term a]
dedc_implication2 b = [a, IMPL a b] --TODO: existential

-- (a->b),(b->c) -> (a->c)
impl_implication3 :: (Eq a) => (Term a,Term a) -> (Term a,Term a) -> [Term a]
impl_implication3 (a,b) (b',c)
  | b == b' = [IMPL a c]
  | otherwise = []
dedc_implication3 :: (Eq a) => (Term a,Term a) -> [Term a]
dedc_implication3 (a,c) = [IMPL a b, IMPL b c] --TODO: existential


--a->(a v b)
impl_disjunction1 :: (Eq a) => Term a -> [Term a]
impl_disjunction1 a = [OR a b] --TODO: existential
dedc_disjunction1 :: (Eq a) => (Term a,Term a) -> [Term a]
dedc_disjunction1 (a,b) = [a]

--b->(a v b)
impl_disjunction2 :: (Eq a) => Term a -> [Term a]
impl_disjunction2 b = [OR a b] --TODO: existential
dedc_disjunction2 :: (Eq a) => (Term a,Term a) -> [Term a]
dedc_disjunction2 (a,b) = [b]

--(a v b),(a->c),(b->c) -> c
impl_disjunction3 :: (Eq a) => (Term a,Term a) -> (Term a,Term a) -> (Term a,Term a) -> [Term a]
impl_disjunction3 (a,b) (a',c) (b',c')
  | a==a' && b==b' && c==c' = [c]
  | otherwise = []
dedc_disjunction3 :: (Eq a) => Term a -> [Term a]
dedc_disjunction3 c = [OR a b, IMPL a c, IMPL b 3] --TODO: existential

-- a,b -> (a ^ b)
impl_conjunction1 :: (Eq a) => Term a -> Term a -> [Term a]
impl_conjunction1 a b = [AND a b]
dedc_conjunction1 :: (Eq a) => (Term a,Term a) -> [Term a]
dedc_conjunction1 (a,b) = [a,b]

-- (a ^ b) -> a
impl_conjunction3 :: (Eq a) => (Term a,Term a) -> [Term a]
impl_conjunction3 (a,b) = [a]
dedc_conjunction3 :: (Eq a) => Term a -> [Term a]
dedc_conjunction3 a = [AND a b] --TODO: existential

-- (a ^ b) -> b
impl_conjunction3 :: (Eq a) => (Term a,Term a) -> [Term a]
impl_conjunction3 (a,b) = [b]
dedc_conjunction3 :: (Eq a) => Term a -> [Term a]
dedc_conjunction3 b = [AND a b] --TODO: existential



--quantifiers--------------------------------

-- exists x t -> t[x/y] where y is a fresh variable bound to the quantifier

-- t[x], x=something bound -> exists x t

-- forall x t -> t[x/y]

-- t[x], x unassigned (no equivalencies or anything) -> forall x t
