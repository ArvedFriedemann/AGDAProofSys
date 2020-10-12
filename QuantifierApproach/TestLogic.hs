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

type StringRawKB = [String]

binds = \bounds -> (bindConstTo $ Map.fromList
  [("/=",NEQ),("=",EQT),("->",IMPL),("^",CONJ),("v",DISJ), ("()", BOT),("bot", BOT),
   ("forall", (VP UNIVERSAL)),("exists", (VP EXISTENTIAL)),("neutral", (VP NEUTRAL)),("name",NAME),("quote",QUOTE),("unquote",UNQUOTE), ("solve", SOLVE)]).(bindConst bounds)
stdrd = \bounds -> (binds bounds).rt

stdVarProp :: (Ord a) => [a] -> a -> VarProp
stdVarProp lst v = if Set.member v (Set.fromList lst)
                   then UNIVERSAL
                   else NEUTRAL


stdcrt :: (Monad m) => [String] -> [String] -> String -> IntBindMonQuanT m OpenTerm
stdcrt bounds universals = (createOpenTerm $ stdVarProp universals).(stdrd bounds)

stdcrtAll :: (Monad m) => [String] -> [String] ->  [String] -> IntBindMonQuanT m [OpenTerm]
stdcrtAll bounds universals trms = createOpenTerms (stdVarProp universals) ((stdrd bounds) <$> trms)

stdkb :: (Monad m) => [String] -> StringRawKB -> IntBindMonQuanT m RawKB
stdkb bounds stringkb = sequence $ [stdcrt bounds [] cls | cls <- stringkb]

stdTest' :: [String] -> StringRawKB -> [String] -> IO (Either MError ())
stdTest' bounds strkb goals = runIntBindQuanT $ do {
  goals <- stdcrtAll bounds [] goals;
  kb <- stdkb bounds strkb;
  interactiveProof [(kb, g) | g <- goals]
}
