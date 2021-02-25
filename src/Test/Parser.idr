module Test.Parser

import Control.ANSI.SGR
import Data.List
import Text.Show.Pretty
import Test.Mini

--------------------------------------------------------------------------------
--          String Tokens
--------------------------------------------------------------------------------

nats : List String
nats = ["0","123","0xabc123","0b11011","0o77653", "0XAFC123"]

strings : List String
strings = map show ["0 foo","x y z", "    ", "\t\t"]

chars : List String
chars = map show ['a','z','A','Z','0','9','\t','ä','ü']

spaceStrs : List String
spaceStrs = ["   ","\r\n","\n","\t\t \n"]

ops : List String
ops = [">>=", "+", "-", ">=", ">", "<", "::", "::="]

idents : List String
idents = ["idents", "nat_token", "Nat_Token", "foo_bar__", "_any123"]

identOrOps : List String
identOrOps = idents ++ map (\o => "(" ++ o ++ ")") ops

symbols : List String
symbols = ["(",")","[","]","{","}",",","="]

doubles : List String
doubles = ["1.234", "12.0e-2", "0.334E+10", "0.1234E10"]

--------------------------------------------------------------------------------
--          Lexing
--------------------------------------------------------------------------------

testLex : String -> List (String, List ShowToken) -> IO ()
testLex s ps = do putStrLn ("Lexing " ++ s)
                  report $ runEq lex (map (map Right) ps)

natTokens : List (String,List ShowToken)
natTokens = map (\s => (s, [NatLit s])) nats

stringTokens : List (String,List ShowToken)
stringTokens = map (\s => (s, [StringLit s])) strings

charTokens : List (String,List ShowToken)
charTokens = map (\s => (s, [CharLit s])) chars

doubleTokens : List (String,List ShowToken)
doubleTokens = map (\s => (s, [DblLit s])) doubles

spaceTokens : List (String,List ShowToken)
spaceTokens = map (\s => (s, [])) spaceStrs

identTokens : List (String,List ShowToken)
identTokens = map (\s => (s, [Ident s])) idents

opTokens : List (String,List ShowToken)
opTokens = map (\s => (s, [Op s])) ops

symbolTokens : List (String,List ShowToken)
symbolTokens = map (\s => (s, [Symbol s])) symbols

export
lexTest : IO ()
lexTest = do testLex "nat literals" natTokens
             testLex "string literals" stringTokens
             testLex "char literals" charTokens
             testLex "float literals" doubleTokens
             testLex "spaces" spaceTokens
             testLex "identifiers" identTokens
             testLex "operators" opTokens
             testLex "symbols" symbolTokens

--------------------------------------------------------------------------------
--          Parsing
--------------------------------------------------------------------------------

testParse : String -> List (String, Value) -> IO ()
testParse s ps = do putStrLn ("Parsing " ++ s)
                    report $ runEq parseValueE (map (map Right) ps)

prims : List (String,Value)
prims =  map (\s => (s, Chr s)) chars
      ++ map (\s => (s, Natural s)) nats
      ++ map (\s => (s, Dbl s)) doubles
      ++ map (\s => (s, Str s)) strings
      ++ map (\s => (s, Con (MkName s) [])) identOrOps

singleCons : List (String,Value)
singleCons = do (s,v) <- prims
                ident <- identOrOps
                pure ( ident ++ " " ++ s
                     , Con (MkName ident) [v]
                     )

doubleCons : List (String,Value)
doubleCons = do (ps,v)  <- prims
                ident   <- identOrOps
                (cs,sc) <- take 100 singleCons
                pure ( ident ++ " " ++ ps ++ "(" ++ cs ++ ")"
                     , Con (MkName ident) [v,sc]
                     )

emptyRecs : List (String,Value)
emptyRecs = do i <- identOrOps
               pure (i ++ " {}", Rec (MkName i) [])

primsOrCons : List (String,Value)
primsOrCons = prims ++ take 10 singleCons ++ take 20 doubleCons

recs1 : List (String,Value)
recs1 = do (ps,p)  <- primsOrCons
           ident1  <- identOrOps
           ident2  <- identOrOps
           pure  ( concat {t = List} [ ident1, " { "
                                     , ident2, " = ", ps
                                     , " } "
                                     ]
                 , Rec (MkName ident1) [(MkName ident2, p)]
                 )

recs2 : List (String,Value)
recs2 = do (ps,p)  <- take 20 primsOrCons
           ident1  <- take 2 identOrOps
           ident2  <- take 2 identOrOps
           ident3  <- take 2 identOrOps
           (cs,sc) <- take 5 doubleCons
           pure  ( concat {t = List} [ ident1, " { "
                                     , ident2, " = ", ps, ", "
                                     , ident3, " = ", cs
                                     , " } "
                                     ]
                 , Rec (MkName ident1) [ (MkName ident2, p)
                                       , (MkName ident3, sc)
                                       ]
                 )

export
parseTest : IO ()
parseTest = do testParse "primities" prims
               testParse "cons arity 1" singleCons
               testParse "cons arity 2" doubleCons
               testParse "empty records" emptyRecs
               testParse "records of arity 1" recs1
               testParse "records of arity 2" recs2
