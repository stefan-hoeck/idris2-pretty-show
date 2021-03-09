module Test.Main

import Test.Parser
import Test.PP

main : IO ()
main = do lexTest
          parseTest
          ppTest
