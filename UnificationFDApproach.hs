{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}

module UnificationFDApproach where

import Control.Unification
import Control.Unification.Types
import Control.Unification.IntVar
import Control.Monad.Identity
import Control.Monad.Trans
import Control.Monad.Trans.Except
import Control.Monad.Trans.Writer
import Control.Monad.State
import Data.Foldable
import Data.Traversable
import Data.List
import Safe

data Constant = TOP | BOT | CON String deriving (Show, Eq)
data Term a = CONST Constant
            | APPL a a
  deriving (Show, Eq, Functor, Foldable, Traversable)

data CTerm a = CCONST Constant | CVAR a | CAPPL (CTerm a) (CTerm a) deriving (Show, Eq)

instance Unifiable Term where
    zipMatch (CONST s1) (CONST s2)       | s1 == s2 = Just $ CONST s1
    zipMatch (APPL a b) (APPL a' b')                = Just $ APPL (Right (a, a')) (Right (b, b'))
    zipMatch _              _                       = Nothing


-- type ClosedTerm = Fix Term
type OpenTerm = UTerm Term IntVar
type IntBinding = IntBindingT Term Identity
type MError = UFailure Term IntVar
type IntBindMon = ExceptT MError IntBinding

runIntBind = runIdentity . evalIntBindingT . runExceptT

con :: Constant -> OpenTerm
con = UTerm . CONST

appl :: OpenTerm -> OpenTerm -> OpenTerm
appl a b = UTerm (APPL a b)

lst :: [OpenTerm] -> OpenTerm
lst [] = UTerm (CONST TOP)
lst (x:y:[]) = UTerm (APPL x y)
lst (x:xs) = UTerm (APPL x (lst xs))

lookout :: (MonadState s m) => m a -> m a
lookout m = do {
  s <- get;
  r <- m;
  put s;
  return r
}

freshVar :: IntBinding OpenTerm
freshVar = UVar <$> freeVar

nubVars :: (Eq a) => CTerm a -> [a]
nubVars ls = nub $ execWriter $ vars' ls

vars' :: (Eq a) => CTerm a -> Writer [a] ()
vars' (CCONST _) = return ()
vars' (CVAR a) = tell [a]
vars' (CAPPL a b) = vars' a >> vars' b

createOpenTerm :: (Eq a) => CTerm a -> IntBinding OpenTerm
createOpenTerm t = do {
  vars <- return $ nubVars t;
  intVars <- sequence $ [freshVar | v <- vars];
  return $ applyCBinding (zip vars intVars) t
}

applyCBinding :: (Eq a) => [(a, OpenTerm)] -> CTerm a -> OpenTerm
applyCBinding asm (CCONST c)  = con c
applyCBinding asm (CVAR v)    = lookupJust v asm
applyCBinding asm (CAPPL a b) = appl (applyCBinding asm a) (applyCBinding asm b)

getPossibleMatches :: [OpenTerm] -> OpenTerm -> IntBindMon [OpenTerm]
getPossibleMatches kb goal = concat <$> (sequence $ [catchE (lookout $ do {u <- unify t goal; return <$> ((applyBindings u) :: IntBindMon OpenTerm)}) (const $ return []) | t <- kb])
