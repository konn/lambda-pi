{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}

module Language.Lambda.Syntax.LambdaPi.ParserSpec where

import Data.List (foldl1')
import Data.Text (Text)
import qualified Data.Text as T
import Language.Lambda.Syntax.LambdaPi
import Language.Lambda.Syntax.LambdaPi.Parser
import Test.Tasty
import Test.Tasty.HUnit

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
  , ("λ x. x", Lam NoExtField "x" Nothing (var "x"))
  , ("(λ x. x)", Lam NoExtField "x" Nothing (var "x"))
  ,
    ( "λ(step: (Π(n: Nat). t n -> t (succ n))). step"
    , Lam
        NoExtField
        "step"
        ( Just $
            Pi NoExtField (DepNamed "n") nat $
              Pi
                NoExtField
                Indep
                (App NoExtField (var "t") (var "n"))
                ( App
                    NoExtField
                    (var "t")
                    ( App
                        NoExtField
                        (Var NoExtField $ PrimName NoExtField Succ)
                        (var "n")
                    )
                )
        )
        (Var NoExtField $ Global NoExtField "step")
    )
  ,
    ( "{a: Nat, b: Nat -> Nat}"
    , Record NoExtField $ RecordFieldTypes [("a", nat), ("b", nat :~> nat)]
    )
  ,
    ( "record {a = Nat, b = succ}"
    , MkRecord NoExtField $ MkRecordFields [("a", nat), ("b", succE)]
    )
  , ("rec.foo", ProjField NoExtField (var "rec") "foo")
  ,
    ( "rec.foo.bar"
    , ProjField NoExtField (ProjField NoExtField (var "rec") "foo") "bar"
    )
  ,
    ( "record { foo = 2 : Nat, quux = Nat -> Nat }.foo.bar"
    , ProjField
        NoExtField
        ( ProjField
            NoExtField
            ( MkRecord NoExtField $
                MkRecordFields
                  [ ("foo", Ann NoExtField (succ' (succ' zero)) nat)
                  , ("quux", nat :~> nat)
                  ]
            )
            "foo"
        )
        "bar"
    )
  ,
    ( "λ (x : rec.foo). x"
    , Lam NoExtField "x" (Just $ ProjField NoExtField (var "rec") "foo") (var "x")
    )
  ,
    ( "let Rec = record { f = succ, ty = Nat -> Nat } in Rec.f 0"
    , Let
        NoExtField
        "Rec"
        (MkRecord NoExtField $ MkRecordFields [("f", succE), ("ty", nat :~> nat)])
        (App NoExtField (ProjField NoExtField (var "Rec") "f") zero)
    )
  , ("(| int : Nat |)", Variant NoExtField $ VariantTags [("int", nat)])
  , -- FIXME: more stylish syntax
    ("(| int = Nat |)", Inj NoExtField "int" nat)
  ]

succE :: Expr Parse
succE = succCon

test_exprP :: TestTree
test_exprP =
  testGroup
    "exprP"
    [ testGroup
        "Regression Test"
        [ testCase src $
          parseOnly exprP (T.pack src) @?= Right expect
        | (src, expect) <- inputCases
        ]
    ]

natElim' :: ParsedExpr
natElim' = Var NoExtField $ PrimName NoExtField NatElim

succ' :: ParsedExpr -> Expr Parse
succ' = App NoExtField succCon

vecElim' :: ParsedExpr
vecElim' =
  Lam NoExtField "a" (Just star)
    $ Lam
      NoExtField
      "t"
      ( Just $
          Pi NoExtField (DepNamed "n") nat $
            Pi
              NoExtField
              Indep
              (Vec NoExtField (var "a") (var "n"))
              star
      )
    $ Lam
      NoExtField
      "base"
      ( Just $ apps [var "t", zero, Nil NoExtField (var "a")]
      )
    $ Lam
      NoExtField
      "ind"
      ( Just $
          Pi NoExtField (DepNamed "n") nat $
            Pi NoExtField (DepNamed "x") (var "a") $
              Pi NoExtField (DepNamed "xs") (Vec NoExtField (var "a") (var "n")) $
                Pi NoExtField Indep (apps [var "t", var "n", var "xs"]) $
                  apps [var "t", App NoExtField succCon (var "n"), Cons NoExtField (var "a") (var "n") (var "x") (var "xs")]
      )
    $ Lam NoExtField "n" (Just nat)
    $ Lam NoExtField "xs" (Just $ Vec NoExtField (var "a") (var "n"))
    $ apps [var "t", var "n", var "xs"]

apps :: [ParsedExpr] -> Expr Parse
apps = foldl1' (App NoExtField)

succCon :: ParsedExpr
succCon = Var NoExtField $ PrimName NoExtField Succ

zero :: ParsedExpr
zero = Var NoExtField $ PrimName NoExtField Zero

nat :: Expr Parse
nat = Var NoExtField $ PrimName NoExtField Nat

star :: Expr Parse
star = Star NoExtField

vecCon' :: ParsedExpr
vecCon' = Lam NoExtField "t" (Just (Star NoExtField)) $ Lam NoExtField "n" (Just nat) $ Vec NoExtField (Var NoExtField $ Global NoExtField "t") (Var NoExtField $ Global NoExtField "n")

pattern (:~>) :: ParsedExpr -> ParsedExpr -> ParsedExpr
pattern (:~>) l r = Pi NoExtField Indep l r

pattern Lam' ::
  (XLam phase ~ NoExtField) =>
  LamBindName phase ->
  LamBindType phase ->
  LamBody phase ->
  Expr phase
pattern Lam' t u v = Lam NoExtField t u v

infixr 0 :~>

vecNat5 :: Expr Parse
vecNat5 = apps [vecCon', nat, succ' (succ' (succ' (succ' (succ' zero))))]

var :: Text -> ParsedExpr
var = Var NoExtField . Global NoExtField
