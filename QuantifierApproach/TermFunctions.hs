module TermFunctions where

import TermData
import Data.Set as Set
import Data.Map as Map
import Data.Maybe
import Data.List
import Control.Monad
import Control.Monad.Trans
import Control.Monad.State
import Control.Unification
import Control.Unification.IntVar
import Control.Monad.Trans.Except

getConstant :: OpenTerm -> Maybe Constant
getConstant (UTerm (CONST c)) = Just c
getConstant _ = Nothing

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

clst :: [CTerm a] -> CTerm a
clst [] = CCONST BOT
clst ls = foldl1 CAPPL ls

oplist :: OpenTerm -> [OpenTerm] -> OpenTerm
oplist op ls = olist (intersperse op ls)

cvars :: (Ord a) => CTerm a -> Set a
cvars (CCONST _) = Set.empty
cvars (CVAR v) = Set.singleton v
cvars (CAPPL a b) = Set.union (cvars a) (cvars b)

ovars :: OpenTerm -> Set IntVar
ovars (UTerm (CONST _)) = Set.empty
ovars (UVar v) = Set.singleton v
ovars (UTerm (APPL a b)) = Set.union (ovars a) (ovars b)

--fails if term is not a variable
getVar :: (Monad m) => OpenTerm -> IntBindMonQuanT m IntVar
getVar (UVar v) = return v
getVar _ = throwE (CustomError "Not a variable")

freshVar :: (Monad m) => IntBindingTT m OpenTerm
freshVar = var <$> freeVar

mapVars :: (a -> b) -> CTerm a -> CTerm b
mapVars fkt (CCONST c) = CCONST c
mapVars fkt (CVAR v) = CVAR (fkt v)
mapVars fkt (CAPPL a b) = CAPPL (mapVars fkt a) (mapVars fkt b)

applyCBind :: (Eq a, Ord a) => Map a b -> CTerm a -> CTerm b
applyCBind asm (CCONST c)  = CCONST c
applyCBind asm (CVAR v)    = CVAR $ fromJust $ Map.lookup v asm
applyCBind asm (CAPPL a b) = CAPPL (applyCBind asm a) (applyCBind asm b)

--not too sure if the OpenTerms are anything special...
applyCBinding :: (Eq a, Ord a) => Map a OpenTerm -> CTerm a -> OpenTerm
applyCBinding asm (CCONST c)  = con c
applyCBinding asm (CVAR v)    = fromJust $ Map.lookup v asm
applyCBinding asm (CAPPL a b) = appl (applyCBinding asm a) (applyCBinding asm b)

toOpenTerm :: CTerm IntVar -> OpenTerm
toOpenTerm (CCONST c)   = con c
toOpenTerm (CVAR v)     = var v
toOpenTerm (CAPPL a b)  = appl (toOpenTerm a) (toOpenTerm b)

fromOpenTerm :: OpenTerm -> CTerm IntVar
fromOpenTerm (UVar i) = CVAR i
fromOpenTerm (UTerm (CONST c)) = CCONST c
fromOpenTerm (UTerm (APPL a b)) = CAPPL (fromOpenTerm a) (fromOpenTerm b)

fromOpenTermVP :: (Monad m) => OpenTerm -> IntBindMonQuanT m (CTerm (IntVar,VarProp))
fromOpenTermVP v@(UVar i) = getProperty i >>= \vp -> return $ CVAR (i,vp)
fromOpenTermVP (UTerm (CONST c)) = return $ CCONST c
fromOpenTermVP (UTerm (APPL a b)) = do {
  a' <- fromOpenTermVP a;
  b' <- fromOpenTermVP b;
  return $ CAPPL a' b'
}

createOpenTerm :: (Monad m, Ord a) => (a -> VarProp) -> CTerm a -> IntBindMonQuanT m OpenTerm
createOpenTerm props term = head <$> createOpenTerms props [term]

createOpenTerms :: (Monad m, Ord a) => (a -> VarProp) -> [CTerm a] -> IntBindMonQuanT m [OpenTerm]
createOpenTerms props terms = do {
  varMap <- Map.fromList <$> sequence [(lift $ freeVar) >>= \v -> return (var, v)
                                    | var <- (Set.toList $ Set.unions (cvars <$> terms))];
  sequence $ [setProperty v (props var) | (var, v) <- Map.toList varMap];
  return $ toOpenTerm <$> (mapVars (\var -> fromJust (Map.lookup var varMap)) ) <$> terms
}

createNeutOpenTerm :: (Monad m) => (Eq a, Ord a) => CTerm a -> IntBindingTT m OpenTerm
createNeutOpenTerm t = head <$> createNeutOpenTerms [t]

createNeutOpenTerms :: (Monad m) => (Eq a, Ord a) => [CTerm a] -> IntBindingTT m [OpenTerm]
createNeutOpenTerms trms = do {
  vars <- return $ Set.unions $ cvars <$> trms;
  intVars <- sequence $ [freshVar | v <- Set.toList vars];
  return $ applyCBinding (Map.fromList $ zip (Set.toList vars) intVars) <$> trms
}

--unify the two terms a b, if a subsumes b. Throws an error if the subsumption failed.
unifySubsumes :: (Monad m) => OpenTerm -> OpenTerm -> IntBindMonQuanT m OpenTerm
unifySubsumes a b = do {
  sub <- subsumes a b;
  if sub
  then unify a b
  else throwE (CustomError "No subsumtion")
}

--checks if the given term is a left-associative binary operator of the given constant. If that is the case it returns the two arguments.
matchBinConst :: (Monad m) => Constant -> OpenTerm -> IntBindMonQuanT m (OpenTerm,OpenTerm)
matchBinConst cst term = do {
                              a <- lift $ freshVar;
                              b <- lift $ freshVar;
                              ot <- return $ olist [a, con cst, b];
                              unifySubsumes ot term; --TODO: Maybe term needs to be extracted...
                              return (a,b)
                            }

matchBinConstLAssocList :: (Monad m) => Constant -> OpenTerm -> IntBindMonQuanT m [OpenTerm]
matchBinConstLAssocList cst term = catchE (do {
  (a,b) <- matchBinConst cst term;
  lst <- applyBindings a >>= matchBinConstLAssocList cst; --TODO: applying should not be necessary!
  b' <- applyBindings b;
  return $ lst ++ [b'];
}) (const $ return [term])

matchBinAppl :: (Monad m) => OpenTerm -> IntBindMonQuanT m (OpenTerm,OpenTerm)
matchBinAppl term = do {
                          a <- lift $ freshVar;
                          b <- lift $ freshVar;
                          ot <- return $ olist [a, b];
                          unifySubsumes ot term;--TODO: Maybe term needs to be extracted...
                          return (a,b)
                        }

matchBinApplLAssocList :: (Monad m) => OpenTerm -> IntBindMonQuanT m [OpenTerm]
matchBinApplLAssocList term = catchE (do {
  (a,b) <- matchBinAppl term;
  lst <- applyBindings a >>= matchBinApplLAssocList; --TODO: applying should not be necessary!
  b' <- applyBindings b;
  return $ lst ++ [b'];
}) (const $ return [term])

----------------------------------------------
--Clauses
----------------------------------------------

clauseToList :: Clause -> [OpenTerm]
clauseToList (prems, post) = prems ++ [post]

listToClause :: [OpenTerm] -> Clause
listToClause lst = (init lst, last lst)

clauseFromList :: [OpenTerm] -> Clause
clauseFromList lst = (init lst, last lst)

clauseToTerm :: Clause -> OpenTerm
clauseToTerm cls = oplist (con IMPL) (clauseToList cls)

kbToTerm :: KB -> OpenTerm
kbToTerm kb = oplist (con CONJ) (clauseToTerm <$> kb)

goalsToKB :: [(KB, OpenTerm)] -> KB
goalsToKB goals = (\(kb, goal) -> clauseFromList $ (clauseToTerm <$> kb) ++ [goal]) <$> goals

goalsToTerm :: [(KB, OpenTerm)] -> OpenTerm
goalsToTerm = kbToTerm.goalsToKB

modifyAsList :: (Monad m) => ([OpenTerm] -> m [OpenTerm]) -> Clause -> m Clause
modifyAsList fkt cls = clauseFromList <$> fkt (clauseToList cls)

applyClause :: (Monad m) => Clause -> IntBindMonQuanT m Clause
applyClause cls = modifyAsList applyBindingsAll cls

applyKB :: (Monad m) => KB -> IntBindMonQuanT m KB
applyKB kb = sequence $ applyClause <$> kb

-----------------------------------------
--Quantifier stuff
-----------------------------------------





isBound :: (Monad m) => IntVar -> IntBindingTT m Bool
isBound var = do {
  masm <- lookupVar var;
  case masm of
    Just t -> return True
    Nothing -> return False
}

--TODO: WARNING: This only checks if universal was bound, but not whether it is equal to another variable (which it cannot be if its universal)
checkUniversalsUnbound :: (Monad m) => OpenTerm -> IntBindMonQuanT m ()
checkUniversalsUnbound trm = checkUniversalsUnboundLst (ovars trm)

checkUniversalsUnboundLst :: (Monad m) => Set IntVar -> IntBindMonQuanT m ()
checkUniversalsUnboundLst vars = void $ sequence [do {
  uniBound <- (&&) <$> (lift $ isBound v) <*> isUniversal v;
  if uniBound
  then throwE (UniversalBoundError v)
  else return ()}
  | v <- Set.toList vars]

runIntBindT :: (Monad m) => IntBindMonT m a -> m (Either MError a)
runIntBindT m = evalIntBindingT $ runExceptT m

runIntBindQuanT :: (Monad m) => IntBindMonQuanT m a -> m (Either MError a)
runIntBindQuanT m = evalStateT (runIntBindT m) Map.empty
