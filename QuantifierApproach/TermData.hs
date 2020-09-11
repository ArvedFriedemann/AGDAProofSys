{-# LANGUAGE CPP, FunctionalDependencies, FlexibleInstances, MultiParamTypeClasses, FlexibleContexts #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# LANGUAGE UndecidableInstances #-}

module TermData where

import Control.Unification
import Control.Unification.IntVar
import Control.Monad.Identity
import Control.Monad.Trans
import Control.Monad.Trans.Except
import Control.Monad.Trans.Writer
import Control.Monad.State
import Data.Foldable
import Data.Traversable
import Data.List
import Data.Map.Lazy as Map
import Safe


data Constant = TOP | BOT | NEQ | EQT | IMPL | CONJ | DISJ | CON String deriving (Show, Eq)
data Term a = CONST Constant
            | APPL a a
  deriving (Show, Eq, Functor, Foldable, Traversable)

instance Unifiable Term where
    zipMatch (CONST s1) (CONST s2)       | s1 == s2 = Just $ CONST s1
    zipMatch (APPL a b) (APPL a' b')                = Just $ APPL (Right (a, a')) (Right (b, b'))
    zipMatch _              _                       = Nothing

--data CTerm a = CCONST Constant | UNIVERSALV a | EXISTENTIALV a | CAPPL (CTerm a) (CTerm a) deriving (Show, Eq)

data CustomError t v =  OccursFailure v (UTerm t v)
                      | MismatchFailure (t (UTerm t v)) (t (UTerm t v))
                      | CustomError String

data VarProp = UNIVERSAL | EXISTENTIAL | NEUTRAL deriving (Show, Eq)

instance Fallible t v (CustomError t v) where
  occursFailure v t     = OccursFailure v t
  mismatchFailure t1 t2 = MismatchFailure t1 t2

class (Monad m) =>  VarProperties v m where
  getProperty :: v -> m VarProp
  setProperty :: v -> VarProp -> m ()

isUniversal :: (VarProperties v m) => v -> m Bool
isUniversal v = getProperty v >>= \p -> return $ p == UNIVERSAL

isExistential :: (VarProperties v m) => v -> m Bool
isExistential v = getProperty v >>= \p -> return $ p == EXISTENTIAL

isNeutral :: (VarProperties v m) => v -> m Bool
isNeutral v = getProperty v >>= \p -> return $ p == NEUTRAL

instance (Monad m) => VarProperties IntVar (IntBindMonQuanT m) where
  getProperty v = do {
    propmap <- lift2 get;
    case Map.lookup (getVarID v) propmap of
      Just prop -> return prop
      Nothing -> return NEUTRAL
  }
  setProperty v prop = lift2 $ modify (Map.insert (getVarID v) prop)

-- type ClosedTerm = Fix Term
type OpenTerm = UTerm Term IntVar
type IntBinding = IntBindingT Term Identity
type MError = CustomError Term IntVar
type IntBindingTT m = IntBindingT Term m
type IntBindMonT m = ExceptT MError (IntBindingTT m)
type PropStateT m = StateT (Map Int VarProp) m
type IntBindMonQuanT m = ExceptT MError (IntBindingTT (PropStateT m))


lift2 :: (MonadTrans t1, MonadTrans t2, Monad m, Monad (t2 m)) =>
          m a -> t1 (t2 m) a
lift2 = lift.lift

lift3 :: (MonadTrans t1, MonadTrans t2, MonadTrans t3, Monad m, Monad (t3 m), Monad (t2 (t3 m))) =>
          m a -> t1 (t2 (t3 m)) a
lift3 = lift.lift.lift
