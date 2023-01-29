module Parser

import Data.List
import Test.Mini
import Text.Parse.Manual
import Text.Show.Pretty

%default total

--------------------------------------------------------------------------------
--          String Tokens
--------------------------------------------------------------------------------

nats : List String
nats = ["0","123","0xabc123","0b11011","0o77653", "0XAFC123"]

strings : List String
strings = map show ["0 foo","x y z", "    ", "\t\t"]

chars : List String
chars = map show (the (List Char) ['a','z','A','Z','0','9','\t','ä','ü'])

spaceStrs : List String
spaceStrs = ["   ","\r\n","\n","\t\t \n"]

ops : List String
ops = [">>=", "+", "-", ">=", ">", "<", "::", "::="]

idents : List String
idents = ["idents", "nat_token", "Nat_Token", "foo_bar__", "_any123"]

identOrOps : List String
identOrOps = idents ++ map (\o => "(\{o})") ops

symbols : List String
symbols = ["(",")","[","]","{","}",",","="]

doubles : List String
doubles = ["1.234", "12.0e-2", "0.334E+10", "0.1234E10"]

mapPair : (a -> b) -> a -> (a,b)
mapPair f x = (x, f x)

mapPairs : Functor f => (a -> b) -> f a -> f (a,b)
mapPairs g = map (mapPair g)

--------------------------------------------------------------------------------
--          Lexing
--------------------------------------------------------------------------------

lex : String -> Either PSErr (List Token)
lex = map (map val) . tokens

testLex : String -> List (String, List Token) -> IO Bool
testLex s ps = do
  putStrLn ("Lexing " ++ s)
  report $ runEq lex (map (map Right) ps)

natTokens : List (String,List Token)
natTokens = mapPairs (pure . Lit . Natural) nats

stringTokens : List (String,List Token)
stringTokens = mapPairs (pure . Lit . Str) strings

charTokens : List (String,List Token)
charTokens = mapPairs (pure . Lit . Chr) chars

doubleTokens : List (String,List Token)
doubleTokens = mapPairs (pure . Lit . Dbl) doubles

spaceTokens : List (String,List Token)
spaceTokens = mapPairs (const []) spaceStrs

identTokens : List (String,List Token)
identTokens = mapPairs (pure . Id . MkName) idents

opTokens : List (String,List Token)
opTokens = mapPairs (pure . Op . MkName) ops

symb : String -> Token
symb "(" = '('
symb ")" = ')'
symb "[" = '['
symb "]" = ']'
symb "{" = '{'
symb "}" = '}'
symb "," = ','
symb "=" = '='
symb s   = Op $ MkName s

symbolTokens : List (String,List Token)
symbolTokens = mapPairs (pure . symb) symbols

export
lexTest : IO Bool
lexTest = testAll [
    testLex "nat literals" natTokens
  , testLex "string literals" stringTokens
  , testLex "char literals" charTokens
  , testLex "float literals" doubleTokens
  , testLex "spaces" spaceTokens
  , testLex "identifiers" identTokens
  , testLex "operators" opTokens
  , testLex "symbols" symbolTokens
  ]

--------------------------------------------------------------------------------
--          Parsing
--------------------------------------------------------------------------------

testParse : String -> List (String, Value) -> IO Bool
testParse s ps = do
  putStrLn ("Parsing " ++ s)
  report $ runEq parseValueE (map (map Right) ps)

prims : List (String,Value)
prims =
     mapPairs Chr chars
  ++ mapPairs Natural nats
  ++ mapPairs Dbl doubles
  ++ mapPairs Str strings
  ++ mapPairs ((`Con` []) . MkName) identOrOps

negated : List (String,Value)
negated =
     map (\s => ("-" ++ s, Neg $ Natural s)) nats
  ++ map (\s => ("-" ++ s, Neg $ Dbl s)) doubles

singleCons : List (String,Value)
singleCons = do
  (s,v) <- prims
  ident <- identOrOps
  pure ("\{ident} \{s}", Con (MkName ident) [v])

doubleCons : List (String,Value)
doubleCons = do
  (ps,v)  <- prims
  ident   <- identOrOps
  (cs,sc) <- take 100 singleCons
  pure ("\{ident} \{ps}(\{cs})", Con (MkName ident) [v,sc])

emptyRecs : List (String,Value)
emptyRecs = do
  i <- identOrOps
  pure ("\{i} {}", Rec (MkName i) [])

primsOrCons : List (String,Value)
primsOrCons = prims ++ take 10 singleCons ++ take 20 doubleCons

recs1 : List (String,Value)
recs1 = do
  (ps,p) <- primsOrCons
  i1     <- MkName <$> identOrOps
  i2     <- MkName <$> identOrOps
  pure ("\{i1} {\{i2} = \{ps} }", Rec i1 [(i2, p)])

rec3 :
     (ps : (String,Value))
  -> (i1,i2,i3 : VName)
  -> (cs : (String,Value))
  -> (String, Value)
rec3 (ps,p) i1 i2 i3 (cs,sc) =
  ("\{i1} {\{i2} = \{ps}, \{i3} = \{cs}}", Rec i1 [(i2, p), (i3, sc)])

export
recs2 : List (String,Value)
recs2 =
  [| rec3
     (List.take 20 primsOrCons)
     (MkName <$> List.take 2 identOrOps)
     (MkName <$> List.take 2 identOrOps)
     (MkName <$> List.take 2 identOrOps)
     (List.take 5 doubleCons)
  |]

export
parseTest : IO Bool
parseTest = testAll
  [ testParse "primitives" prims
  , testParse "negated" negated
  , testParse "cons arity 1" singleCons
  , testParse "cons arity 2" doubleCons
  , testParse "empty records" emptyRecs
  , testParse "records of arity 1" recs1
  , testParse "records of arity 2" recs2
  ]
