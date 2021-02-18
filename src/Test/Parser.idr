module Test.Parser

import Control.ANSI.SGR
import Generics.Derive
import Text.Show.Value

%language ElabReflection

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

testLex : String -> List (String, List ShowToken) -> IO ()
testLex s ps = do putStrLn ("Lexing " ++ s)
                  report $ run tst ps
  where tst : (String, List ShowToken) -> Maybe String
        tst (s,ts) = let res = lex s
                      in if res == Right ts then Nothing
                                            else Just $ show res

nats : List (String,List ShowToken)
nats = map (\s => (s, [NatLit s])) ["0","123","0xabc123","0b11011","0o77653"]

export
lexTest : IO ()
lexTest = do testLex "nat literals" nats
