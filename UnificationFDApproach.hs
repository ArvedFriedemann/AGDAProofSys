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

data Constant = TOP | BOT | EQT | IMPL | CON String deriving (Show, Eq)
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
olist :: [OpenTerm] -> OpenTerm
olist [] = UTerm (CONST TOP)
olist ls = foldl1 (\x y -> UTerm (APPL x y)) ls

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

--like lookout, but returning a value if there is one.
lookoutCatch :: (Monad m) => IntBindMonT m a -> IntBindMonT m [a]
lookoutCatch m = lookout $ catch m

--wraps the value into a list in case it cannot be created
catch :: (Monad m) => IntBindMonT m a -> IntBindMonT m [a]
catch m = catchE (return <$> m) (const $ return [])

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

createOpenTerms :: (Monad m) => (Eq a) => [CTerm a] -> IntBindingTT m [OpenTerm]
createOpenTerms trms = do {
  vars <- return $ nub $ concatMap nubVars trms;
  intVars <- sequence $ [freshVar | v <- vars];
  return $ applyCBinding (zip vars intVars) <$> trms
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


mapVars :: (a -> b) -> CTerm a -> CTerm b
mapVars fkt (CCONST c) = CCONST c
mapVars fkt (CVAR v) = CVAR (fkt v)
mapVars fkt (CAPPL a b) = CAPPL (mapVars fkt a) (mapVars fkt b)

--getPossibleMatches :: (Monad m) => [OpenTerm] -> OpenTerm -> IntBindMonT m [OpenTerm]
--getPossibleMatches kb goal = concat <$> (sequence $ [catchE (lookout $ do {u <- unify t goal; return <$> ((applyBindings u) :: IntBindMonT m OpenTerm)}) (const $ return []) | t <- kb])



---------------------------------------------------------
--pretty printing
---------------------------------------------------------
niceNameMultConst = 9
niceNames :: [String]
niceNames = niceNames' 0
niceNames' :: Int -> [String]
niceNames' 0 = niceNames' 1
niceNames' 1 = (take 26 $ return <$> ['a'..]) ++ (map ("x" ++) (show <$> [1..]))
niceNames' n = (concat [zipWith (++) (replicate n letter) (show <$> [1..])| letter <- take 26 $ return <$> ['a'..]] ) ++ (map ("x" ++) (show <$> [1..]))

intVarToInt :: IntVar -> Int
intVarToInt (IntVar i) = i

giveNiceIntNames :: CTerm IntVar -> CTerm String
giveNiceIntNames = mapVars ((\x -> (niceNames' niceNameMultConst) !! x).(\x -> x `mod` (26 * niceNameMultConst)).intVarToInt)
  where niceNameMultConst = 9

giveNiceNames :: (Eq a) => CTerm a -> CTerm String
giveNiceNames t = applyCBind asm t
  where vars = nubVars t
        asm = zip vars niceNames

ppCTerm :: CTerm String -> String
ppCTerm t = execWriter $ ppCTerm' t

ppCTerm' :: CTerm String -> Writer String ()
ppCTerm' (CCONST TOP) = tell "T"
ppCTerm' (CCONST BOT) = tell "()"
ppCTerm' (CCONST EQT) = tell "="
ppCTerm' (CCONST IMPL) = tell "->"
ppCTerm' (CCONST (CON s)) = tell s
ppCTerm' (CVAR v) = tell v
ppCTerm' (CAPPL a b@(CAPPL a' b')) = ppCTerm' a >> tell " (" >> ppCTerm' b >> tell ")"
ppCTerm' (CAPPL a b) = ppCTerm' a >> tell " " >> ppCTerm' b

bindConst :: [String] -> CTerm String -> CTerm String
bindConst lst = bindConstTo ((\x -> (x, CON x)) <$> lst)

bindConstTo :: [(String,Constant)] -> CTerm String -> CTerm String
bindConstTo bnds (CCONST (CON s)) = case lookup s bnds of
                                      Just c' -> CCONST c'
                                      Nothing -> CCONST (CON s)
bindConstTo bnds (CCONST c) = CCONST c
bindConstTo bnds (CVAR x) = case lookup x bnds of
                              Just c' -> CCONST c'
                              Nothing -> CVAR x
bindConstTo bnds (CAPPL a b) = CAPPL (bindConstTo bnds a) (bindConstTo bnds b)

oTToString :: OpenTerm -> String
oTToString t = ppCTerm $ giveNiceIntNames $ fromOpenTerm t

----------------------------------
--testing stuff
----------------------------------
{-
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
-}
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



-------------------------------------------------------------
--Util
-------------------------------------------------------------

lift2 :: (MonadTrans t1, MonadTrans t2, Monad m, Monad (t2 m)) =>
          m a -> t1 (t2 m) a
lift2 = lift.lift
