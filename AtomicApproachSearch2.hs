module AtomicApproachSearch2 where

import AtomicApproach2
import Control.Monad.State.Lazy

type VarState p a = State [p] a

getVar :: VarState p p
getVar = do {
  (x:xs) <- get;
  put (xs);
  return x
}



data Constants p = CONSTANTS {bot :: p,
                    op_and :: p,
                    op_or :: p,
                    op_impl :: p}

--gives out a pointer to the variable content or the application. Also gives out the new constraints
term_pointer :: SemTerm p -> VarState p (p, [SemTerm p])
term_pointer (SVAR v) = return (v,[])
term_pointer (SAPPL a b) = do {
  p <- getVar;
  return $ (p, [SEMEQ p (a,b)])
}

--The second return argument is the top level term that can be given a variable if needed.
bake_rich_term :: Constants p -> RichTerm p -> VarState p ([SemTerm p], SemTerm p)
bake_rich_term c BOT = return $ ([SVAR (bot c)], SVAR (bot c))
bake_rich_term c (TRM (RVAR p)) = return $ ([SVAR p], SVAR p)
bake_rich_term c (TRM (RAPPL a b)) = do {
  (part1, t1) <- bake_rich_term c (TRM a);
  (part2, t2) <- bake_rich_term c (TRM b);
  (part3, p1) <- term_pointer t1;
  (part4, p2) <- term_pointer t2;
  return $ ((SAPPL p1 p2):(part1++part2++part3++part4), SAPPL p1 p2);
}
bake_rich_term c (EQT a b) = do {
  (part1, t1) <- bake_rich_term c (TRM a);
  (part2, t2) <- bake_rich_term c (TRM b);
  (part3, p1) <- term_pointer t1;
  (part4, p2) <- term_pointer t2;
  return $ ((SEQ a b):(part1++part2++part3++part4), SEQ a b);
}
bake_rich_term c (AND a b) = bake_op (op_and c) a b
bake_rich_term c (OR a b) = bake_op (op_or c) a b
bake_rich_term c (IMPL a b) = bake_op (op_impl c) a b
bake_rich_term c (EXISTS fkt) = do {
  p <- getVar;
  bake_rich_term (fkt p)
}

bake_op :: p -> SemTerm p -> SemTerm p -> VarState p ([SemTerm p], SemTerm p)
bake_op op a b = do {
  (part1, p1) <- term_pointer a;
  (part2, p2) <- term_pointer b;
  (part3, pappl) <- term_pointer (SAPPL op p2)
  return $ ((SAPPL a pappl): (part1++part2++part3), SAPPL a pappl)
}

-- TODO: How to express proper term equality like a=(b,c) with only var and appl
--Maybe do have just normal terms but with addresses as variables. Maybe these addresses can also have subaddresses to address subterms correctly.
--yup...tertiary connection needed
