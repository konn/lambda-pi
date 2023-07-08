{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}

module Language.Lambda.Syntax.LambdaPi.TypingSpec where

import Data.Maybe (fromJust)
import Data.Text (Text)
import Language.Lambda.Syntax.LambdaPi
import Language.Lambda.Syntax.LambdaPi.Eval (vSucc, vZero, (@@))
import Language.Lambda.Syntax.LambdaPi.Parser
import Language.Lambda.Syntax.LambdaPi.Rename
import Language.Lambda.Syntax.LambdaPi.Typing
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
  ,
    ( inf "λ(a: Type) (n: Nat). nil a"
    , VPi (AlphaName "z") VStar $ \z ->
        VPi (AlphaName "l") VNat $ \_ ->
          VVec z vZero
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
  ]

inf :: Text -> Expr Inferable
inf = fromJust . toInferable . renameExpr . either error id . parseOnly exprP

test_typeInfer :: TestTree
test_typeInfer =
  testGroup
    "typeInfer"
    [ testCase (show $ parens (pprint e)) $
      case typeInfer 0 mempty e of
        Left err -> assertFailure $ "Typing error: " <> err
        Right (ty0, _) -> ty0 @?= ty
    | (e, ty) <- infCases
    ]

test_typeCheck :: TestTree
test_typeCheck =
  testGroup
    "typeCheck"
    [ testCase (show $ parens (pprint e)) $
      case typeCheck 0 mempty (XExpr $ Inf e) ty of
        Left err -> assertFailure $ "Typing error: " <> err
        Right _ev' -> pure ()
    | (e, ty) <- infCases
    ]
