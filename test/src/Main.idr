module Main

import Control.ANSI.SGR
import Test.Mini
import Parser
import PP
import System

main : IO ()
main = do
  res <- testAll [ lexTest, parseTest, ppTest ]
  if res
    then putStrLn (foreground Green "\n\nAll tests passed") >> exitSuccess
    else putStrLn (foreground Red "\n\nSome tests failed") >> exitFailure
