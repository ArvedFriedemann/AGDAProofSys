module Util where

import TermFunctions
import TermData
import Control.Monad.Trans.Except
import Control.Monad.State


allSucceeding :: (Monad m) => [IntBindMonQuanT m a] -> IntBindMonQuanT m [a]
allSucceeding mons = (map fst) <$> possibleActions mons

--tries out every action (always backtracking to the original state) and returns the action paired with the result they'd give. A generalised lookout or allSucceeding. BACKTRACKS IN ALL CASES!
possibleActions:: (Monad m) => [IntBindMonQuanT m a] -> IntBindMonQuanT m [(a,IntBindMonQuanT m a)]
possibleActions acts = concat <$> (sequence [lookoutCatch ((\r -> (r, m)) <$> m) | m <- acts])

--like lookout, but returning a value if there is one.
lookoutCatch :: (Monad m) => IntBindMonQuanT m a -> IntBindMonQuanT m [a]
lookoutCatch m = lookout $ catch m

--wraps the value into a list in case it cannot be created
catch :: (Monad m) => IntBindMonQuanT m a -> IntBindMonQuanT m [a]
catch m = catchE (return <$> m) (const $ return [])

lookout :: (MonadState s m) => m a -> m a
lookout m = do {
  s <- get;
  r <- m;
  put s;
  return r
}
