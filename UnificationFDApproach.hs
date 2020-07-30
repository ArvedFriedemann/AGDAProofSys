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

import Text.Parsec hiding (spaces)

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
type IntBindingTT m = IntBindingT Term m
type IntBindMonT m = ExceptT MError (IntBindingTT m)

runIntBind = runIdentity . evalIntBindingT . runExceptT
runIntBindState = runIdentity . runIntBindingT . runExceptT
runIntBindT :: (Monad m) => IntBindMonT m a -> m (Either MError a)
runIntBindT m = evalIntBindingT $ runExceptT m

con :: Constant -> OpenTerm
con = UTerm . CONST

scon :: String -> OpenTerm
scon s = UTerm (CONST (CON s))

appl :: OpenTerm -> OpenTerm -> OpenTerm
appl a b = UTerm (APPL a b)

--TODO! This should be a foldl, not foldr! WARNING!
list :: [OpenTerm] -> OpenTerm
list [] = UTerm (CONST TOP)
list ls = foldl1 (\x y -> UTerm (APPL x y)) ls

clst :: [CTerm a] -> CTerm a
clst [] = CCONST BOT
clst ls = foldl1 CAPPL ls

lookout :: (MonadState s m) => m a -> m a
lookout m = do {
  s <- get;
  r <- m;
  put s;
  return r
}

freshVar :: (Monad m) => IntBindingTT m OpenTerm
freshVar = UVar <$> freeVar

nubVars :: (Eq a) => CTerm a -> [a]
nubVars ls = nub $ execWriter $ vars' ls

vars' :: (Eq a) => CTerm a -> Writer [a] ()
vars' (CCONST _) = return ()
vars' (CVAR a) = tell [a]
vars' (CAPPL a b) = vars' a >> vars' b

createOpenTerm :: (Monad m) => (Eq a) => CTerm a -> IntBindingTT m OpenTerm
createOpenTerm t = do {
  vars <- return $ nubVars t;
  intVars <- sequence $ [freshVar | v <- vars];
  return $ applyCBinding (zip vars intVars) t
}

fromOpenTerm :: OpenTerm -> CTerm IntVar
fromOpenTerm (UVar i) = CVAR i
fromOpenTerm (UTerm (CONST c)) = CCONST c
fromOpenTerm (UTerm (APPL a b)) = CAPPL (fromOpenTerm a) (fromOpenTerm b)

--not too sure if the OpenTerms are anything special...
applyCBinding :: (Eq a) => [(a, OpenTerm)] -> CTerm a -> OpenTerm
applyCBinding asm (CCONST c)  = con c
applyCBinding asm (CVAR v)    = lookupJust v asm
applyCBinding asm (CAPPL a b) = appl (applyCBinding asm a) (applyCBinding asm b)

applyCBind :: (Eq a) => [(a, b)] -> CTerm a -> CTerm b
applyCBind asm (CCONST c)  = CCONST c
applyCBind asm (CVAR v)    = CVAR $ lookupJust v asm
applyCBind asm (CAPPL a b) = CAPPL (applyCBind asm a) (applyCBind asm b)


--getPossibleMatches :: (Monad m) => [OpenTerm] -> OpenTerm -> IntBindMonT m [OpenTerm]
--getPossibleMatches kb goal = concat <$> (sequence $ [catchE (lookout $ do {u <- unify t goal; return <$> ((applyBindings u) :: IntBindMonT m OpenTerm)}) (const $ return []) | t <- kb])



---------------------------------------------------------
--pretty printing
---------------------------------------------------------
niceNames = (take 26 (return <$> ['a'..])) ++ (map ("x" ++) (show <$> [1..]))

giveNiceNames :: (Eq a) => CTerm a -> CTerm String
giveNiceNames t = applyCBind asm t
  where vars = nubVars t
        asm = zip vars niceNames

ppCTerm :: CTerm String -> String
ppCTerm t = execWriter $ ppCTerm' t

ppCTerm' :: CTerm String -> Writer String ()
ppCTerm' (CCONST TOP) = tell "T"
ppCTerm' (CCONST BOT) = tell "()"
ppCTerm' (CCONST (CON s)) = tell s
ppCTerm' (CVAR v) = tell v
ppCTerm' (CAPPL a b@(CAPPL a' b')) = tell "(" >> ppCTerm' a >> tell ") " >> ppCTerm' b
ppCTerm' (CAPPL a b) = ppCTerm' a >> tell " " >> ppCTerm' b

bindConst :: [String] -> CTerm String -> CTerm String
bindConst bnds (CCONST c) = CCONST c
bindConst bnds (CVAR x)
    | x `elem` bnds = CCONST (CON x)
    | otherwise = CVAR x
bindConst bnds (CAPPL a b) = CAPPL (bindConst bnds a) (bindConst bnds b)

----------------------------------
--testing stuff
----------------------------------
bounds = ["=","^","->","v"]
binds = bindConst bounds
testkb = binds <$> rt <$> ["a = a", "b = b", "(a ^ (a -> b)) -> b"]
testgoal = binds $ rt $ "(k k) = (l m)"

test1 = runIntBind $ do {
  kb <- sequence $ lift <$> createOpenTerm <$> testkb;
  goal <- lift $ createOpenTerm testgoal;
  --mts <- getPossibleMatches kb goal;
  --return $ ppCTerm <$> giveNiceNames <$> fromOpenTerm <$> mts
  return ()
}

----------------------------------
--parsing
----------------------------------

forbiddenSymb = "() \t\n`"
spaceChars = " \t"

idfr::Parsec String st String
idfr = many1 (noneOf forbiddenSymb)

baseTerm::Parsec String st (CTerm String)
baseTerm = (try $ string "()" >> return (CCONST BOT)) <|> (try $ parens term) <|> (CVAR <$> idfr)

term::Parsec String st (CTerm String)
term = clst <$> (spaces >> sepEndBy1 baseTerm spaces1)

parens::Parsec String st a -> Parsec String st a
parens p = do {string "("; r <- p; string ")"; return r}

spaces::Parsec String st String
spaces = many (oneOf spaceChars)

spaces1::Parsec String st String
spaces1 = many1 (oneOf spaceChars)

safeParse::Parsec [a] () b -> [a] -> b
safeParse p ipt = case parse p "" ipt of
                    Right v -> v
                    Left err -> error (show err)

termFromString::String -> CTerm String
termFromString = safeParse term
rt::String -> CTerm String
rt = termFromString


freshTermFromString :: (Monad m) => String -> IntBindingTT m OpenTerm
freshTermFromString = freshTermFromString' []
freshTermFromString' :: (Monad m) => [String] -> String -> IntBindingTT m OpenTerm
freshTermFromString' bnds s = createOpenTerm $ bindConst bnds $ rt s
