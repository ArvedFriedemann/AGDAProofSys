module AtomicApproach where

import Data.Either

data Term p = VAR p | APPL p p deriving (Eq, Show)
data RichTerm p = BOT | TRM (Term p)
                  | EQ    p p
                  | AND   (Term p) (Term p)
                  | OR    (Term p) (Term p)
                  | IMPL  (Term p) (Term p)
                  | EXISTS (p -> RichTerm p)

type P a p = (p, a)

bin_match :: (Eq p) => p -> Term p -> Maybe (Term p, Term p)
bin_match op (APPL a (APPL op' b))
  | op==op' = Just (a,b)
  | otherwise = Nothing

--a=a
impl_eq1 :: (Eq p) => p -> [RichTerm p]
impl_eq1 a = [EQ a a]
dedc_eq1 :: (Eq p) => p -> p -> [RichTerm p]
dedc_eq1 a b
  | a==b = []
  | otherwise = [EQ a b]

--a=b -> b=a
impl_eq2 :: (Eq p) => p -> p -> [RichTerm p]
impl_eq2 a b = [EQ b a]
dedc_eq2 :: (Eq p) => p -> p -> [RichTerm p]
dedc_eq2 a b = [EQ b a]

--a=b b=c -> a=c           --problematic...only works with pointer equality.
impl_eq3 :: (Eq p) => p -> p -> p -> p -> [RichTerm p]
impl_eq3 a b b' c
  | b==b' = [EQ a c]
  | otherwise = []

dedc_eq3 :: (Eq p) => p -> p -> [RichTerm p]
dedc_eq3 a c = [EXISTS (\b -> AND (EQ a b) (EQ b c))]
