module TestLogic where

import TermData
import TermFunctions
import Interaction
import Printing

import Data.List
import Data.Map as Map
import Data.Set as Set
import Control.Monad
import Control.Monad.Trans
import Debug.Trace

type StringRawKB = [String]

stdbounds = [("/=",NEQ),("=",EQT),("->",IMPL),("^",CONJ),("v",DISJ), ("T", TOP),("()", BOT),("bot", BOT),
 ("forall", (VP UNIVERSAL)),("exists", (VP EXISTENTIAL)),("neutral", (VP NEUTRAL)),("name",NAME),("quote",QUOTE),("unquote",UNQUOTE), ("solve", SOLVE)]

binds :: [String] -> CTerm String -> CTerm String
binds bounds = (bindConstTo $ Map.fromList stdbounds).(bindConst bounds)

stdrd = \bounds -> (binds bounds).rt

allbounds :: [String] -> [OpenTerm]
allbounds customBounds = (con <$> snd <$> stdbounds) ++ (con <$> CON <$> customBounds)

boundsIneqForm :: [OpenTerm] -> [OpenTerm]
boundsIneqForm bounds = [olist [(olist [x, con EQT, y]),con IMPL, con BOT] |(xi, x) <- idxbounds, (yi, y) <- idxbounds, xi /= yi]
  where idxbounds = zip [0..] bounds

stdVarProp :: (Ord a) => [a] -> a -> VarProp
stdVarProp lst v = if Set.member v (Set.fromList lst)
                   then UNIVERSAL
                   else NEUTRAL

exclVarProp :: (Ord a) => [a] -> a -> VarProp
exclVarProp lst v = if Set.member v (Set.fromList lst)
                    then UNIVERSAL
                    else EXISTENTIAL


stdcrt :: (Monad m) => [String] -> [String] -> String -> IntBindMonQuanT m OpenTerm
stdcrt bounds universals = stdcrt' bounds (stdVarProp universals)

stdcrt' :: (Monad m) => [String] -> (String -> VarProp) -> String -> IntBindMonQuanT m OpenTerm
stdcrt' bounds vpfkt = (createOpenTerm $ vpfkt).(stdrd bounds)

stdcrtAll :: (Monad m) => [String] -> [String] ->  [String] -> IntBindMonQuanT m [OpenTerm]
stdcrtAll bounds universals = stdcrtAll' bounds (stdVarProp universals)

stdcrtAll' :: (Monad m) => [String] -> (String -> VarProp) ->  [String] -> IntBindMonQuanT m [OpenTerm]
stdcrtAll' bounds vpfkt trms = createOpenTerms vpfkt ((stdrd bounds) <$> trms)

stdkb :: (Monad m) => [String] -> StringRawKB -> IntBindMonQuanT m RawKB
stdkb bounds stringkb =
  ((++) $ boundsIneqForm (allbounds bounds)) <$>
  (sequence $ [stdcrt bounds [] cls | cls <- stringkb])

stdkbuniv :: (Monad m) => [String] -> StringRawKB -> IntBindMonQuanT m RawKB
stdkbuniv bounds stringkb =
  ((++) $ boundsIneqForm (allbounds bounds)) <$>
  (sequence $ [stdcrt' bounds (const UNIVERSAL) cls | cls <- stringkb])

stdTest' :: Bool -> [String] -> StringRawKB -> [String] -> IO (Either MError ())
stdTest' kbuniv bounds strkb goals = runIntBindQuanT $ do {
  goals <- stdcrtAll bounds [] goals;
  kb <- (if kbuniv
          then stdkbuniv bounds strkb
          else stdkb bounds strkb);
  interactiveProof kb [(kb, g) | g <- goals]
}
