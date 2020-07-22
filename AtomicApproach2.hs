module AtomicApproach2 where

import Data.Either

data Term p = VAR p | APPL p p deriving (Eq, Show)
data RecTerm p = RVAR p | RAPPL (RecTerm p) (RecTerm p) deriving (Eq, Show)
data SemTerm p = SVAR p | SAPPL p p | SEQ p p | SEMEQ p (p,p) deriving (Eq, Show)
data RichTerm p = BOT | TRM (RecTerm p)
                  | EQT    (RichTerm p) (RichTerm p)
                  | AND   (RichTerm p) (RichTerm p)
                  | OR    (RichTerm p) (RichTerm p)
                  | IMPL  (RichTerm p) (RichTerm p)
                  | EXISTS (p -> RichTerm p)

type P a p = (p, a)

bin_match :: (Eq p) => p -> Term p -> Maybe (Term p, Term p)
bin_match op (APPL a (APPL op' b))
  | op==op' = Just (a,b)
  | otherwise = Nothing

--a=a
impl_eq1 :: (Eq p) => p -> [RichTerm p]
impl_eq1 a = [EQT a a]
dedc_eq1 :: (Eq p) => p -> p -> [RichTerm p]
dedc_eq1 a b
  | a==b = []
  | otherwise = [EQT a b]

--a=b -> b=a
impl_eq2 :: (Eq p) => p -> p -> [RichTerm p]
impl_eq2 a b = [EQT b a]
dedc_eq2 :: (Eq p) => p -> p -> [RichTerm p]
dedc_eq2 a b = [EQT b a]

--a=b b=c -> a=c           --problematic...only works with pointer equality.
impl_eq3 :: (Eq p) => p -> p -> p -> p -> [RichTerm p]
impl_eq3 a b b' c
  | b==b' = [EQT a c]
  | otherwise = []

dedc_eq3 :: (Eq p) => p -> p -> [RichTerm p]
dedc_eq3 a c = [EXISTS (\b -> AND (EQT a b) (EQT b c))]
