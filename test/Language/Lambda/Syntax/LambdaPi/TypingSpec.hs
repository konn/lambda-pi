{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}

module Language.Lambda.Syntax.LambdaPi.TypingSpec where

import qualified Data.Bifunctor as Bi
import Data.Maybe (fromJust)
import Data.Text (Text)
import Language.Lambda.Syntax.LambdaPi
import Language.Lambda.Syntax.LambdaPi.Eval (vSucc, vZero, (@@))
import Language.Lambda.Syntax.LambdaPi.Parser
import Language.Lambda.Syntax.LambdaPi.Rename
import Language.Lambda.Syntax.LambdaPi.Typing
import RIO (evaluateDeep, rnf)
import Test.Tasty
import Test.Tasty.HUnit
import Text.PrettyPrint (parens)

(~>) :: Type -> Type -> Type
l ~> r = VPi Anonymous l (const r)

infCases :: [(Expr Inferable, Type)]
infCases =
  [
    ( inf "λ(a: Type) (x: a). x"
    , VPi
        (AlphaName "x")
        VStar
        (\v -> VPi (AlphaName "a") v $ const v)
    )
  , (inf "natElim (λ n. ℕ) 3 (λ k. succ) 2", VNat)
  ,
    ( inf "λ(t: Nat -> Type) (step: Π(n: Nat). t n -> t (succ n)) (x: t 0). step 0 x"
    , VPi (AlphaName "f") (VPi Anonymous VNat $ const VStar) $ \f ->
        VPi
          (AlphaName "succ")
          ( VPi (AlphaName "k") VNat $ \k ->
              VPi Anonymous (f @@ k) (const $ f @@ (vSucc @@ k))
          )
          $ \_ -> VPi (AlphaName "base") (f @@ vZero) $
            \_ ->
              f @@ (vSucc @@ vZero)
    )
  ,
    ( inf "natElim"
    , VPi (AlphaName "f") (VNat ~> VStar) $ \f ->
        VPi (AlphaName "f0") (f @@ vZero) $ \_ ->
          VPi
            (AlphaName "fsucc")
            ( VPi (AlphaName "l") VNat $ \l ->
                VPi (AlphaName "fl") (f @@ l) $ \_ ->
                  f @@ (vSucc @@ l)
            )
            $ \_ ->
              VPi (AlphaName "m") VNat $ \n ->
                f @@ n
    )
  ,
    ( inf "λ (t: Nat -> Type) (base: t 0) (step : Π(n : Nat). t n -> t (succ n)) (k : Nat). natElim t base step k"
    , VPi (AlphaName "f") (VNat ~> VStar) $ \f ->
        VPi (AlphaName "f0") (f @@ vZero) $ \_ ->
          VPi
            (AlphaName "fsucc")
            ( VPi (AlphaName "l") VNat $ \l ->
                VPi (AlphaName "fl") (f @@ l) $ \_ ->
                  f @@ (vSucc @@ l)
            )
            $ \_ ->
              VPi (AlphaName "m") VNat $ \n ->
                f @@ n
    )
  ,
    ( inf "λ (a : Type) (n : Nat) (f : a -> a). natElim (λ _. a -> a) (λ x. x) (λ _ fn x. f (fn x)) n"
    , VPi (AlphaName "a") VStar $ \a ->
        VPi (AlphaName "n") VNat $ \_n ->
          VPi (AlphaName "f") (a ~> a) $ \_f ->
            a ~> a
    )
  ,
    ( inf "(λ (a : Type) (n : Nat) (f : a -> a). natElim (λ _. a -> a) (λ x. x) (λ _ fn x. f (fn x)) n) Nat"
    , VPi (AlphaName "n") VNat $ \_n ->
        VPi (AlphaName "f") (VNat ~> VNat) $ \_f ->
          VNat ~> VNat
    )
  ]

pattern VNat :: Value
pattern VNat = VNeutral (NFree VStar (PrimName NoExtField Nat))

chkCases :: [(Expr Checkable, Type)]
chkCases =
  [(chk "natElim (λ n. ℕ) 3 (λ k. succ) 2", VNat)]

inf :: Text -> Expr Inferable
inf = fromJust . toInferable . renameExpr . either error id . parseOnly exprP

chk :: Text -> Expr Checkable
chk = fromJust . toCheckable . renameExpr . either error id . parseOnly exprP

test_typeInfer :: TestTree
test_typeInfer =
  testGroup
    "typeInfer"
    [ testCaseSteps (show $ parens (pprint e)) $ \step ->
      case typeInfer mempty e of
        Left err -> assertFailure $ "Typing error: " <> err
        Right (ty0, eTy) -> do
          step "Check if type matches"
          ty0 @?= ty
          step $ "Typed term: " <> show (pprint eTy)
          step "Check if typed expr doesn't contain bottom"
          evaluateDeep $ rnf eTy
    | (e, ty) <- infCases
    ]

test_typeCheck :: TestTree
test_typeCheck =
  testGroup
    "typeCheck"
    [ testCaseSteps (show $ parens (pprint e)) $ \step -> do
      step "check type"
      case typeCheck mempty e ty of
        Left err -> assertFailure $ "Typing error: " <> err
        Right eTy -> do
          step "Check if typed term dosn't contain bottom"
          evaluateDeep $ rnf eTy
    | (e, ty) <- map (Bi.first $ XExpr . Inf) infCases ++ chkCases
    ]
