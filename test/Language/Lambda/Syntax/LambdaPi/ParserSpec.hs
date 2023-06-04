{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PatternSynonyms #-}

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
  , ("natElim", LamAnn (Inf (Pi (Inf Nat) (Inf Star))) (LamAnn (Inf (Bound 0 :@: Inf Zero)) (LamAnn (Inf (Pi (Inf Nat) (Inf (Pi (Inf (Bound 2 :@: Inf (Bound 0))) (Inf (Bound 3 :@: Inf (Succ (Inf (Bound 1))))))))) (LamAnn (Inf Nat) (NatElim (Inf (Bound 3)) (Inf (Bound 2)) (Inf (Bound 1)) (Inf (Bound 0)))))))
  , ("Vec Nat 5", vecNat5)
  , ("(Vec Nat) 5", vecNat5)
  , ("(Vec Nat 5)", vecNat5)
  ]

vecNat5 :: Term 'Inferable
vecNat5 =
  LamAnn (Inf Star) (LamAnn (Inf Nat) (Vec (Inf (Bound 1)) (Inf (Bound 0))))
    :@: Inf Nat
    :@: Inf (SuccI (SuccI (SuccI (SuccI (SuccI Zero)))))

pattern SuccI :: Term 'Inferable -> Term 'Inferable
pattern SuccI n = Succ (Inf n)

checkableCases :: [(String, Term 'Checkable)]
checkableCases =
  [ ("λ x. x", Lam $ Inf $ Bound 0)
  , ("(λ x. x)", Lam $ Inf $ Bound 0)
  ]

test_checkableExprP :: TestTree
test_checkableExprP =
  testGroup
    "checkableExprP"
    [ testGroup
        "Regression Test"
        [ testCase src $
          parseOnly checkableExprP (T.pack src) @?= Right expect
        | (src, expect) <- map (Bi.second Inf) inferableCases <> checkableCases
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
