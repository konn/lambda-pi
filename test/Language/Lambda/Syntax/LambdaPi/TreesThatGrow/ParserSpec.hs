{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}

module Language.Lambda.Syntax.LambdaPi.TreesThatGrow.ParserSpec where

import Data.List (foldl1')
import Data.Text (Text)
import qualified Data.Text as T
import Language.Lambda.Syntax.LambdaPi.TreesThatGrow
import Language.Lambda.Syntax.LambdaPi.TreesThatGrow.Parser
import Test.Tasty
import Test.Tasty.HUnit

type ParsedExpr = Expr Parse

natElim' :: ParsedExpr
natElim' =
  Lam "t" (Just (Pi NoExtField Nothing nat star))
    $ Lam "base" (Just (App NoExtField (var "t") zero))
    $ Lam
      "ind"
      ( Just
          ( Pi
              NoExtField
              (Just "k")
              nat
              ( Pi
                  NoExtField
                  Nothing
                  (App NoExtField (var "t") (var "k"))
                  $ App NoExtField (var "t")
                  $ succ' (var "k")
              )
          )
      )
    $ Lam "n" (Just nat)
    $ NatElim NoExtField (var "t") (var "base") (var "ind") (var "n")

vecElim' :: ParsedExpr
vecElim' =
  Lam "a" (Just star)
    $ Lam
      "t"
      ( Just $
          Pi NoExtField (Just "n") nat $
            Pi
              NoExtField
              Nothing
              (Vec NoExtField (var "a") (var "n"))
              star
      )
    $ Lam
      "base"
      ( Just $ apps [var "t", zero, Nil NoExtField (var "a")]
      )
    $ Lam
      "ind"
      ( Just $
          Pi NoExtField (Just "n") nat $
            Pi NoExtField (Just "x") (var "a") $
              Pi NoExtField (Just "xs") (Vec NoExtField (var "a") (var "n")) $
                Pi NoExtField Nothing (apps [var "t", var "n", var "xs"]) $
                  apps [var "t", Succ NoExtField (var "n"), Cons NoExtField (var "a") (var "n") (var "x") (var "xs")]
      )
    $ Lam "n" (Just nat)
    $ Lam "xs" (Just $ Vec NoExtField (var "a") (var "n"))
    $ apps [var "t", var "n", var "xs"]

apps :: [ParsedExpr] -> Expr Parse
apps = foldl1' (App NoExtField)

succ' :: ParsedExpr -> ParsedExpr
succ' = Succ NoExtField

zero :: ParsedExpr
zero = Zero NoExtField

nat :: Expr Parse
nat = Nat NoExtField

star :: Expr Parse
star = Star NoExtField

vecCon' :: ParsedExpr
vecCon' = Lam "t" (Just (Star NoExtField)) $ Lam "n" (Just (Nat NoExtField)) $ Vec NoExtField (Var NoExtField "t") (Var NoExtField "n")

pattern (:~>) :: ParsedExpr -> ParsedExpr -> ParsedExpr
pattern (:~>) l r = Pi NoExtField Nothing l r

infixr 0 :~>

inputCases :: [(String, Expr Parse)]
inputCases =
  [ ("Nat : Type", Ann NoExtField nat star)
  , ("(Nat : Type)", Ann NoExtField nat star)
  ,
    ( "Vec Nat 0"
    , apps [vecCon', nat, zero]
    )
  , ("(Vec Nat 0)", apps [vecCon', nat, zero])
  , ("Nat", nat)
  , ("(Nat)", nat)
  , ("((Nat))", nat)
  , ("Nat -> Nat", nat :~> nat)
  , ("(Nat -> Nat)", nat :~> nat)
  , ("Nat -> Nat -> Nat", nat :~> nat :~> nat)
  , ("Nat -> (Nat -> Nat)", nat :~> nat :~> nat)
  , ("(Nat -> Nat -> Nat)", nat :~> nat :~> nat)
  , ("(Nat -> (Nat -> Nat))", nat :~> nat :~> nat)
  , ("(Nat -> Nat) -> Nat", (nat :~> nat) :~> nat)
  , ("((Nat -> Nat) -> Nat)", (nat :~> nat) :~> nat)
  , ("natElim", natElim')
  , ("Vec Nat 5", vecNat5)
  , ("(Vec Nat) 5", vecNat5)
  , ("(Vec Nat 5)", vecNat5)
  , ("x", var "x")
  , ("(x)", var "x")
  , ("λ x. x", Lam "x" Nothing (var "x"))
  , ("(λ x. x)", Lam "x" Nothing (var "x"))
  ]

vecNat5 :: Expr Parse
vecNat5 = apps [vecCon', nat, SuccI (SuccI (SuccI (SuccI (SuccI zero))))]

pattern SuccI :: ParsedExpr -> ParsedExpr
pattern SuccI n = Succ NoExtField n

test_checkableExprP :: TestTree
test_checkableExprP =
  testGroup
    "checkableExprP"
    [ testGroup
        "Regression Test"
        [ testCase src $
          parseOnly exprP (T.pack src) @?= Right expect
        | (src, expect) <- inputCases
        ]
    ]

var :: Text -> ParsedExpr
var = Var NoExtField