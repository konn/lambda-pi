{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}

module Language.Lambda.Syntax.LambdaPi.RenameSpec where

import Language.Lambda.Syntax.LambdaPi
import Language.Lambda.Syntax.LambdaPi.Parser
import Language.Lambda.Syntax.LambdaPi.Rename
import Test.Tasty
import Test.Tasty.HUnit

type ParsedExpr = Expr Parse

inputCases :: [(Expr Parse, Expr Rename)]
inputCases =
  [
    ( Lam NoExtField "f" Nothing $
        Lam NoExtField "x" Nothing $
          App NoExtField (var $ Global NoExtField "f") (var $ Global NoExtField "x")
    , Lam NoExtField (AlphaName "f") Nothing $
        Lam NoExtField (AlphaName "x") Nothing $
          App NoExtField (var $ Bound NoExtField 1) (var $ Bound NoExtField 0)
    )
  ]

test_renameExpr :: TestTree
test_renameExpr =
  testGroup
    "exprP"
    [ testGroup
        "Regression Test"
        [ testCase (show inp) $
          renameExpr inp @?= expect
        | (inp, expect) <- inputCases
        ]
    ]

var :: XVar p ~ NoExtField => Name p -> Expr p
var = Var NoExtField
