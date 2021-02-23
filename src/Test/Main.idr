module Test.Main

import Test.Parser

main : IO ()
main = do lexTest
          parseTest
