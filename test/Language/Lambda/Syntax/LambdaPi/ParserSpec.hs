module Language.Lambda.Syntax.LambdaPi.ParserSpec where

import qualified Data.Text as T
import Language.Lambda.Syntax.LambdaPi
import Language.Lambda.Syntax.LambdaPi.Parser
import Test.Tasty
import Test.Tasty.HUnit

test_checkableExprP :: TestTree
test_checkableExprP =
  testGroup
    "checkableExprP"
    [ testGroup
        "Regression Test"
        [ testCase src $
          parseOnly checkableExprP (T.pack src) @?= Right expect
        | (src, expect) <-
            [ ("Nat -> Nat", Inf $ Pi (Inf Nat) $ Inf Nat)
            , ("(Nat -> Nat)", Inf $ Pi (Inf Nat) $ Inf Nat)
            , ("Nat", Inf Nat)
            , ("(Nat)", Inf Nat)
            , ("((Nat))", Inf Nat)
            ]
        ]
    ]