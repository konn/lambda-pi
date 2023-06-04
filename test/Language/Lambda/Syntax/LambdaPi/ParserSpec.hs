{-# LANGUAGE DataKinds #-}

module Language.Lambda.Syntax.LambdaPi.ParserSpec where

import qualified Data.Bifunctor as Bi
import qualified Data.Text as T
import Language.Lambda.Syntax.LambdaPi
import Language.Lambda.Syntax.LambdaPi.Parser
import Test.Tasty
import Test.Tasty.HUnit

inferableCases :: [(String, Term 'Inferable)]
inferableCases =
  [ ("Nat", Nat)
  , ("(Nat)", Nat)
  , ("((Nat))", Nat)
  , ("Nat -> Nat", Pi (Inf Nat) $ Inf Nat)
  , ("(Nat -> Nat)", Pi (Inf Nat) $ Inf Nat)
  , ("Nat -> Nat -> Nat", Pi (Inf Nat) $ Inf $ Pi (Inf Nat) (Inf Nat))
  , ("Nat -> (Nat -> Nat)", Pi (Inf Nat) $ Inf $ Pi (Inf Nat) (Inf Nat))
  , ("(Nat -> Nat -> Nat)", Pi (Inf Nat) $ Inf $ Pi (Inf Nat) (Inf Nat))
  , ("(Nat -> (Nat -> Nat))", Pi (Inf Nat) $ Inf $ Pi (Inf Nat) (Inf Nat))
  , ("(Nat -> Nat) -> Nat", Pi (Inf $ Pi (Inf Nat) (Inf Nat)) $ Inf Nat)
  , ("((Nat -> Nat) -> Nat)", Pi (Inf $ Pi (Inf Nat) (Inf Nat)) $ Inf Nat)
  ]

test_checkableExprP :: TestTree
test_checkableExprP =
  testGroup
    "checkableExprP"
    [ testGroup
        "Regression Test"
        [ testCase src $
          parseOnly checkableExprP (T.pack src) @?= Right expect
        | (src, expect) <- map (Bi.second Inf) inferableCases
        ]
    ]

test_inferableExprP :: TestTree
test_inferableExprP =
  testGroup
    "inferableExprP"
    [ testGroup
        "Regression Test"
        [ testCase src $
          parseOnly inferableExprP (T.pack src) @?= Right expect
        | (src, expect) <- inferableCases
        ]
    ]
