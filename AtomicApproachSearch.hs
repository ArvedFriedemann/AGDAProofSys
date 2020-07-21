module AtomicApproachSearch where

import AtomicApproach

--these are curried  versions of the deduction rules (in their directions, respectively)
--needed such that every rule only has one premise and one posterior.
impl_rules = [curr_impl_eq1, curr_impl_eq2,...]
dedc_rules = [curr_dedc_eq1, curr_dedc_eq2,...]

bidirectional_search :: (Eq a) => [Term a] -> [Term a] -> [Term a]
bidirectional_search knowledge goals
  | knowledge `intersect` goals /= [] = --path from knowledge to goals
  | otherwise = bidirectional_search (impl_rules <*> knowledge) (dedc_rules <*> goals)

--goal: not even to have explicit search. Should be done by atoms on top. Instructions that are just executed once they are top level.
