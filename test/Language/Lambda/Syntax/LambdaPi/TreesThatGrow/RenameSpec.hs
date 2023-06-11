{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}

module Language.Lambda.Syntax.LambdaPi.TreesThatGrow.RenameSpec where

import Language.Lambda.Syntax.LambdaPi.TreesThatGrow
import Language.Lambda.Syntax.LambdaPi.TreesThatGrow.Rename
import Test.Tasty
import Test.Tasty.HUnit

type ParsedExpr = Expr Parse

inputCases :: [(Expr Parse, Expr Rename)]
inputCases =
  [
    ( Lam "f" Nothing $
        Lam "x" Nothing $
          App NoExtField (var "f") (var "x")
    , Lam NoExtField Nothing $
        Lam NoExtField Nothing $
          App NoExtField (var $ Local 1) (var $ Local 0)
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

var :: XVar p ~ NoExtField => Id p -> Expr p
var = Var NoExtField
