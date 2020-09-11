module TermFunctions where

import TermData
import Data.Set as Set
import Data.Map as Map
import Data.Maybe
import Data.List
import Control.Monad.Trans
import Control.Unification
import Control.Unification.IntVar

con :: Constant -> OpenTerm
con = UTerm . CONST

var :: IntVar -> OpenTerm
var = UVar

scon :: String -> OpenTerm
scon s = UTerm (CONST (CON s))

appl :: OpenTerm -> OpenTerm -> OpenTerm
appl a b = UTerm (APPL a b)

olist :: [OpenTerm] -> OpenTerm
olist [] = UTerm (CONST TOP)
olist ls = foldl1 (\x y -> UTerm (APPL x y)) ls

oplist :: OpenTerm -> [OpenTerm] -> OpenTerm
oplist op ls = olist (intersperse op ls)

cvars :: (Ord a) => CTerm a -> Set a
cvars (CCONST _) = Set.empty
cvars (CVAR v) = Set.singleton v
cvars (CAPPL a b) = Set.union (cvars a) (cvars b)

freshVar :: (Monad m) => IntBindingTT m OpenTerm
freshVar = var <$> freeVar

mapVars :: (a -> b) -> CTerm a -> CTerm b
mapVars fkt (CCONST c) = CCONST c
mapVars fkt (CVAR v) = CVAR (fkt v)
mapVars fkt (CAPPL a b) = CAPPL (mapVars fkt a) (mapVars fkt b)

toOpenTerm :: CTerm IntVar -> OpenTerm
toOpenTerm (CCONST c)   = con c
toOpenTerm (CVAR v)     = var v
toOpenTerm (CAPPL a b)  = appl (toOpenTerm a) (toOpenTerm b)

fromCTerms :: (Monad m, Ord a) => (a -> VarProp) -> [CTerm a] -> IntBindMonQuanT m [OpenTerm]
fromCTerms props terms = do {
  varMap <- Map.fromList <$> sequence [(lift $ freeVar) >>= \v -> return (var, v)
                                    | var <- (Set.toList $ Set.unions (cvars <$> terms))];
  sequence $ [setProperty v (props var) | (var, v) <- Map.toList varMap];
  return $ toOpenTerm <$> (mapVars (\var -> fromJust (Map.lookup var varMap)) ) <$> terms
}
