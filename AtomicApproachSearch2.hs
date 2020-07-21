module AtomicApproachSearch2 where

import AtomicApproach2
import Control.Monad.State.Lazy

type VarState p a = State [p] a

getVar :: VarState p p
getVar = do {
  (x:xs, mp) <- get;
  put (xs, mp);
  return x
}



data Constants p = {bot :: p,
                    op_and :: p,
                    op_or :: p,
                    op_impl :: p}

bake_rich_term :: Constants p -> RichTerm p -> VarState p [Term p]
bake_rich_term c BOT = return $ VAR (bot c)
bake_rich_term c (TERM t) = --TODO
bake_rich_term c (AND a b) = bake_op (op_and c) a b
...
bake_richt_term c (EXISTS fkt) = do {
  p <- getVar;
  bake_rich_term (fkt p)
}

bake_op :: p -> Term p -> Term p -> VarState p [Term p]
bake_op op a b = do {
  [pa,pop,pb] <- sequence $ replicate 3 getVar;
  return [APPL pa pop, APPL op pb, EQ pa a, EQ pb b, EQ pop (APPL op pb)]
}

-- TODO: How to express proper term equality like a=(b,c) with only var and appl
--Maybe do have just normal terms but with addresses as variables. Maybe these addresses can also have subaddresses to address subterms correctly.
--yup...tertiary connection needed
