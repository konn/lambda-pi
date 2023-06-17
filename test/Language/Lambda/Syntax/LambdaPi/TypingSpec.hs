{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}

module Language.Lambda.Syntax.LambdaPi.TypingSpec where

import Data.Maybe (fromJust)
import Data.Text (Text)
import Language.Lambda.Syntax.LambdaPi
import Language.Lambda.Syntax.LambdaPi.Eval ((@@))
import Language.Lambda.Syntax.LambdaPi.Parser
import Language.Lambda.Syntax.LambdaPi.Rename
import Language.Lambda.Syntax.LambdaPi.Typing
import Test.Tasty
import Test.Tasty.HUnit
import Text.PrettyPrint (colon, parens, (<+>))

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
          VVec z VZero
    )
  ,
    ( inf "natElim"
    , VPi (AlphaName "f") (VNat ~> VStar) $ \f ->
        VPi (AlphaName "f0") (f @@ VZero) $ \_ ->
          VPi
            (AlphaName "fsucc")
            ( VPi (AlphaName "l") VNat $ \l ->
                VPi (AlphaName "fl") (f @@ l) $ \_ ->
                  f @@ VSucc l
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
    [ testCase (show $ parens (pprint e) <+> colon <+> parens (pprint ty)) $
      case typeInfer 0 mempty e of
        Left err -> assertFailure $ "Typing error: " <> err
        Right (ty0, _) -> ty0 @?= ty
    | (e, ty) <- infCases
    ]
