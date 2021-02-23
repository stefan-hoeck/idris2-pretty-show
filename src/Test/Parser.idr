module Test.Parser

import Control.ANSI.SGR
import Generics.Derive
import Text.Show.Value

%language ElabReflection

%runElab derive "Value" [Generic,Meta,Show,Eq]

--------------------------------------------------------------------------------
--          Mini Test Framework
--------------------------------------------------------------------------------

public export
record Result t where
  constructor MkResult
  ok     : List t
  failed : List (t, String)

%runElab derive "Result" [Generic,Meta,Show,Eq,Semigroup,Monoid]

public export
run : (f : t -> Maybe String) -> List t -> Result t
run f = concatMap run'
  where run' : t -> Result t
        run' t = maybe (MkResult [t] [])
                       (\s => MkResult [] [(t,s)])
                       (f t)

--------------------------------------------------------------------------------
--          ANSI Colorings and Reporting
--------------------------------------------------------------------------------

export
foreground : Color -> String -> String
foreground c s = escapeSGR [SetForeground c] ++ s ++ escapeSGR [Reset]

export
greenOk : String
greenOk =   "[" ++ foreground Green "OK" ++ "]      "

export
redFailed : String
redFailed = "[" ++ foreground Red   "Failed" ++ "]  "

export
spaces : String
spaces = "          "

export
report : Show t => Result t -> IO ()
report (MkResult ok [])     = putStrLn $ greenOk ++ show (length ok) ++ " tests run"
report (MkResult ok failed) = putStrLn $ redFailed ++ details
  where details : String
        details = unlines $  [ show (length ok + length failed) ++ " tests run"
                             , spaces ++ show (length failed) ++ " tests failed"
                             ]
                          ++ map (\(t,s) => spaces ++ show t ++ ": " ++ s) failed

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
                  report $ run tst ps
  where tst : (String, List ShowToken) -> Maybe String
        tst (s,ts) = let res = lex s
                      in if res == Right ts then Nothing
                                            else Just $ show res

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
                    report $ run tst ps
  where tst : (String, Value) -> Maybe String
        tst (s,ts) = let res = parseValueE s
                      in if res == Right ts then Nothing
                                            else Just $ show res

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

export
parseTest : IO ()
parseTest = do testParse "primities" prims
               testParse "cons arity 1" singleCons
               testParse "cons arity 2" doubleCons
