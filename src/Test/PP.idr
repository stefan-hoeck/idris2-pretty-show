module Test.PP

import Text.Show.Pretty
import Test.Mini

[IdShow] Show String where
  show = id

testPP : String -> List (String,String) -> IO ()
testPP s ps = do putStrLn ("Pretty printing " ++ s)
                 report $ runEq (\v => ppShow @{IdShow} v) ps

pair : a -> (a,a)
pair x = (x, x)

export
ppTest : IO ()
ppTest = do testPP "naturals" $ map pair ["0","123","10000"]

            testPP "chars" $ map pair ["'a'", "'0'", "'Z'"]

            testPP "doubles" $ map pair ["1.232", "1.0e-12", "16.5E3"]

            testPP "strings" $ map pair ["\"1.232\"", "\"ab cde\"", "\"foo\""]

            testPP "negative" $ map pair ["-12", "-1.233e12", "-0"]

            testPP "lists" [ ("[1,2,3]", "[ 1 , 2 , 3 ]")
                           , ("[]", "[]")
                           , ("['a','b','c']", "[ 'a' , 'b' , 'c' ]")
                           ]
            testPP "identifiers" $
              map pair ["Ident", "Foo", "H", "_foo"]

            testPP "arity 1 cons" $
              map pair ["Ident 12", "Foo 'a'", "H ()", "_foo 1.22"]

            testPP "arity 2 cons" $
              map pair ["Ident 12 'a'", "Foo 'a' \"bar\"", "H () 12", "_foo 1.22 -1"]

            testPP "nexted cons" $
              map pair ["Ident 12 (Foo 'a') (Maybe 12)"
                       , "Foo (Left 'a') (MkPair \"bar \" 1.20)"
                       , "Bracket (TH 12) (Element 12 _)"
                       ]
