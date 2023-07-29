{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}

module Language.Lambda.Syntax.LambdaPi.EvalSpec where

import Data.Maybe (fromJust)
import Data.Text (Text)
import Language.Lambda.Syntax.LambdaPi
import Language.Lambda.Syntax.LambdaPi.Eval
import Language.Lambda.Syntax.LambdaPi.Parser
import Language.Lambda.Syntax.LambdaPi.Rename
import Language.Lambda.Syntax.LambdaPi.Typing
import Test.Tasty
import Test.Tasty.HUnit
import Text.PrettyPrint (parens)

five :: Value
five = iterate (vSucc @@) vZero !! 5

evalCases :: (HasCallStack) => [(Expr Eval, Value)]
evalCases =
  [ (inferred "5", five)
  , (inferred "natElim (λ n. ℕ) 3 (λ k. succ) 2", five)
  , (inferred "natElim (λ n. ℕ) 3 (λ k n. succ n) 2", five)
  ]

(~>) :: Type -> Type -> Type
l ~> r = VPi Anonymous l (const r)

inf :: (HasCallStack) => Text -> Expr Inferable
inf = fromJust . toInferable . renameExpr . either error id . parseOnly exprP

inferred :: (HasCallStack) => Text -> Expr Eval
inferred = either error snd . typeInfer mempty . inf

newtype VerboseValue = VerboseValue {getValue :: Value}
  deriving newtype (Eq)

instance Show VerboseValue where
  showsPrec _ (VerboseValue v) = shows (v, quote 0 v)

test_eval :: TestTree
test_eval =
  testGroup
    "eval"
    [ testCaseSteps (show $ parens (pprint e)) $ \step -> do
      step $ "typed term: " <> show e
      step "eval"
      VerboseValue (eval mempty e) @?= VerboseValue val
    | (e, val) <- evalCases
    ]
