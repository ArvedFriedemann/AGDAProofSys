-- in reply to http://www.reddit.com/r/haskell/comments/23dxli/why_are_examples_completely_absent_from_hackage/
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}

import Control.Unification
import Control.Unification.Types
import Control.Unification.IntVar
import Control.Monad.Identity
import Control.Monad.Trans
import Control.Monad.Except
import Data.Foldable
import Data.Traversable


-- simple type constructors
data Term a = Con String   -- ^ constant types such as "Int" and "String"
            | Pair (a, a)  -- ^ pairs. Each `a` stands for a `Term a`.
  deriving (Show, Eq, Functor, Foldable, Traversable)

instance Unifiable Term where
    zipMatch (Con s1)       (Con s2)       | s1 == s2 = Just $ Con s1
    zipMatch (Pair (x1,y1)) (Pair (x2,y2))            = Just $ Pair (Right (x1, x2), Right (y1, y2))
    zipMatch _              _                         = Nothing


-- type ClosedTerm = Fix Term
type OpenTerm = UTerm Term IntVar
type IntBinding = IntBindingT Term Identity

con :: String -> OpenTerm
con = UTerm . Con

pair :: (OpenTerm, OpenTerm) -> OpenTerm
pair = UTerm . Pair


-- the pairs (a, Int) and (String, b), which unify to (String, Int)
unifiable_pairs :: IntBinding (OpenTerm, OpenTerm)
unifiable_pairs = do v1 <- freeVar
                     v2 <- freeVar
                     let t1 = pair (UVar v1, con "Int")
                     let t2 = pair (con "String", UVar v2)
                     return (t1, t2)

unify_pairs :: ExceptT (UFailure Term IntVar) IntBinding OpenTerm
unify_pairs = do (t1, t2) <- lift unifiable_pairs
                 r <- unify t1 t2  -- Pair v1 v2, plus bindings saying:
                                   --   v1 = con "String"
                                   --   v2 = con "Int"
                 applyBindings r

-- |
-- >>> main
-- Right (Pair (Con "String",Con "Int"))
main :: IO ()
main = print $ (runIdentity . evalIntBindingT . runExceptT) unify_pairs
