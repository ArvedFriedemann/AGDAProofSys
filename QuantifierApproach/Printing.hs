module Printing where

import Prelude hiding (lookup)

import Util
import TermData
import TermFunctions
--import InferenceRules

import Control.Unification.Types
import Control.Unification.IntVar
import Control.Unification
import Text.Parsec hiding (spaces)
import Control.Monad.Trans.Except
import Control.Monad.Trans.Writer
import Control.Monad.State
import Data.Set as Set hiding (map, take)
import Data.Map as Map hiding (map, take)

-------------------------
--Pretty Printing
-------------------------

clauseToString :: Clause -> String
clauseToString cls = oTToString $ clauseToTerm cls

kbToFormatString :: KB -> String
kbToFormatString kb = unlines (clauseToString <$> kb)

-------------------------
--Output
-------------------------
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

giveNiceNames :: (Eq a, Ord a) => CTerm a -> CTerm String
giveNiceNames t = applyCBind asm t
  where vars = Set.toList $ cvars t
        asm = Map.fromList $ zip vars niceNames

ppCTerm :: CTerm String -> String
ppCTerm t = execWriter $ ppCTerm' t

ppCTermVP :: Map String VarProp -> CTerm String -> String
ppCTermVP m t = execWriter $ ppCTerm' m t

ppCTerm' :: Map String VarProp -> CTerm String -> Writer String ()
ppCTerm' _ (CCONST TOP) = tell "T"
ppCTerm' _ (CCONST BOT) = tell "()"
ppCTerm' _ (CCONST EQT) = tell "="
ppCTerm' _ (CCONST NEQ) = tell "/="
ppCTerm' _ (CCONST IMPL) = tell "->"
ppCTerm' _ (CCONST CONJ) = tell "^"
ppCTerm' _ (CCONST DISJ) = tell "v"
ppCTerm' _ (CCONST FORALL) = tell "forall"
ppCTerm' _ (CCONST EXISTS) = tell "exists"
ppCTerm' _ (CCONST (CON s)) = tell s
ppCTerm' m (CVAR v) = case Map.lookup v m of
                        Just UNIVERSAL -> tell "*" >> tell v
                        Just _ -> tell v
                        Nothing -> tell v
ppCTerm' m (CAPPL a b@(CAPPL a' b')) = ppCTerm' m a >> tell " (" >> ppCTerm' m b >> tell ")"
ppCTerm' m (CAPPL a b) = ppCTerm' m a >> tell " " >> ppCTerm' m b

bindConst :: [String] -> CTerm String -> CTerm String
bindConst lst = bindConstTo (Map.fromList $ (\x -> (x, CON x)) <$> lst)

bindConstTo :: Map String Constant -> CTerm String -> CTerm String
bindConstTo bnds (CCONST (CON s)) = case lookup s bnds of
                                      Just c' -> CCONST c'
                                      Nothing -> CCONST (CON s)
bindConstTo bnds (CCONST c) = CCONST c
bindConstTo bnds (CVAR x) = case lookup x bnds of
                              Just c' -> CCONST c'
                              Nothing -> CVAR x
bindConstTo bnds (CAPPL a b) = CAPPL (bindConstTo bnds a) (bindConstTo bnds b)

oTToString :: OpenTerm -> String
oTToString t = ppCTerm (Map.empty) $ giveNiceIntNames $ fromOpenTerm t

oTToStringMap :: Map String VarProp -> OpenTerm -> String
oTToStringMap m t = ppCTerm m $ giveNiceIntNames $ fromOpenTerm t

oTToStringVP :: (Monad m) => OpenTerm -> IntBindMonQuanT m String
oTToStringVP ot = do {
  ct <- fromOpenTermVP ot;
  propmap <- return $ Map.fromList $ Set.toList $ cvars ct;
  oTToStringMap propmap ot
}


-------------------------
--Parsing
-------------------------

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
freshTermFromString' bnds s = createNeutOpenTerm $ bindConst bnds $ rt s
