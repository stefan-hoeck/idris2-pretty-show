||| A minimalistic testing framework with pretty priting
||| and (not yet implemented) value diffing.
module Test.Mini

import Control.ANSI.SGR
import Derive.Prelude
import Text.Show.Pretty

%language ElabReflection

--------------------------------------------------------------------------------
--          Test Results
--------------------------------------------------------------------------------

namespace Success

  ||| A successful test case
  public export
  record Success i o where
    constructor MkSuccess
    input  : i
    result : o

  %runElab derive "Success" [Show,Eq,PrettyVal]

namespace Failure

  ||| A failed test case
  public export
  record Failure i o where
    constructor MkFailure
    input    : i
    result   : o
    expected : o

  %runElab derive "Failure" [Show,Eq,PrettyVal]


public export
record Result i o where
  constructor MkResult
  ok     : List (Success i o)
  failed : List (Failure i o)

%runElab derive "Result" [Show,Eq,PrettyVal]

export
Semigroup (Result i o) where
  MkResult o1 f1 <+> MkResult o2 f2 = MkResult (o1 ++ o2) (f1 ++ f2)

export
Monoid (Result i o) where neutral = MkResult [] []

--------------------------------------------------------------------------------
--          Running Tests
--------------------------------------------------------------------------------

public export
run :  Foldable t
    => (f : i -> Either (Failure i o) (Success i o))
    -> t i
    -> Result i o
run f = concatMap run'
  where run' : i -> Result i o
        run' inp = case f inp of
                        (Left x)  => MkResult [] [x]
                        (Right x) => MkResult [x] []

public export
runEq : (Foldable t, Eq o) => (f : i -> o) -> t (i,o) -> Result i o
runEq f = concatMap run'
  where run' : (i,o) -> Result i o
        run' (inp,exp) = let res = f inp
                          in if exp == res
                                then MkResult [MkSuccess inp exp] []
                                else MkResult [] [MkFailure inp res exp]

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
report : PrettyVal i => PrettyVal o => Result i o -> IO Bool
report (MkResult ok [])      =
  putStrLn (greenOk ++ show (length ok) ++ " tests run") $> True

report (MkResult ok (f::fs)) =
  do putStrLn (redFailed ++ summary)
     putStrLn "First failure"
     dumpIO f
     pure False
  where summary : String
        summary = unlines [ show (length ok + length fs + 1) ++ " tests run"
                          , spaces ++ show (length fs + 1) ++ " tests failed"
                          ]

export
testAll : List (IO Bool) -> IO Bool
testAll = map and . traverse (map delay)
