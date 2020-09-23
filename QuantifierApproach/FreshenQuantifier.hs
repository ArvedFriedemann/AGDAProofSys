--code taken from the original library and modified to allow freshening only universal variables

{-# LANGUAGE CPP, MultiParamTypeClasses, FlexibleContexts #-}
{-# OPTIONS_GHC -Wall -fwarn-tabs -fno-warn-name-shadowing #-}

-- HACK: in GHC 7.10, Haddock complains about unused imports; but,
-- if we use CPP to avoid including them under Haddock, then it
-- will fail!
#ifdef __HADDOCK__
{-# OPTIONS_GHC -fno-warn-unused-imports #-}
#endif

module FreshenQuantifier where

import TermData
import Control.Unification

import Prelude
    hiding (mapM, mapM_, sequence, foldr, foldr1, foldl, foldl1, all, and, or)

import qualified Data.IntMap as IM
import Data.Traversable
#if __GLASGOW_HASKELL__ < 710
import Control.Applicative
#endif
import Control.Monad.Trans  (MonadTrans(..))
#if (MIN_VERSION_mtl(2,2,1))
-- aka: transformers(0,4,1)
import Control.Monad.Except (MonadError(..))
#else
import Control.Monad.Error  (MonadError(..))
#endif
import Control.Monad.State  (MonadState(..), evalStateT)
import Control.Monad.State.UnificationExtras

freshenUniversal trm = head <$> freshenAllUniversal [trm]

freshenAllUniversal
    ::  ( BindingMonad t v m
        , Fallible t v e
        , MonadTrans em
        , Functor (em m) -- Grr, Monad(em m) should imply Functor(em m)
        , MonadError e (em m)
        , Traversable s
        , VarProperties v (em m)
        )
    => s (UTerm t v)        -- ^
    -> em m (s (UTerm t v)) -- ^
freshenAllUniversal ts0 = evalStateT (mapM loop ts0) IM.empty
    where
    loop t0 = do
        t0 <- lift . lift $ semiprune t0
        case t0 of
            UTerm t -> UTerm <$> mapM loop t
            UVar  v -> do
                let i = getVarID v
                seenVars <- get
                isUni <- lift $ isUniversal v
                case IM.lookup i seenVars of
                    Just (Right t) -> return t
                    Just (Left  t) -> lift . throwError $ occursFailure v t
                    Nothing -> do
                        mb <- lift . lift $ lookupVar v
                        case mb of
                            Nothing -> do
                                -- fresh variable should only be created iff it is universal.
                                v' <- if isUni then lift . lift $ UVar <$> freeVar else return (UVar v)
                                --v' <- lift . lift $ UVar <$> freeVar
                                put $! IM.insert i (Right v') seenVars
                                return v'
                            Just t  -> do
                                put $! IM.insert i (Left t) seenVars
                                t' <- loop t
                                --v' <- if isUni then lift . lift $ UVar <$> newVar t' else return (UVar v)
                                --WARNING: I assume the new variable here is so that the whole assigned term is being copied...this should still happen, no matter if variable is universal or not. Sure, if a universal variable is assigned that should give an error, but at a different point.
                                v' <- lift . lift $ UVar <$> newVar t'
                                modify' $ IM.insert i (Right v')
                                return v'
