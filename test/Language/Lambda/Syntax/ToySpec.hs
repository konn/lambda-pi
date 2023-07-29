{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Language.Lambda.Syntax.ToySpec (test_quoteUnquote) where

import Control.Monad ((<=<))
import Data.Function (on)
import Data.Ord (comparing)
import Data.Void (Void)
import Language.Lambda.Syntax.Toy
import qualified Test.Falsify.Generator as F
import Test.Falsify.Predicate ((.$))
import qualified Test.Falsify.Predicate as P
import qualified Test.Falsify.Range as F
import Test.Tasty
import Test.Tasty.Falsify

test_quoteUnquote :: TestTree
test_quoteUnquote =
  testProperty "quote 0 . unquote ≡ id" $ do
    ClosedTerm t <- gen $ closedTerm $ F.between (0, 100)
    collect "depth" [depth t]
    collect "width" [width t]
    assert $ P.eq .$ ("t", ClosedTerm t) .$ ("quote 0 (unquote t)", ClosedTerm $ quote 0 (unquote t))

-- >>> take 10 $ sample' colosedDeBruijn

depth :: DeBruijn' v -> Word
depth Var {} = 0
depth Local {} = 0
depth (AppDB l r) = depth l + depth r + 1
depth (LamDB e) = 1 + depth e

width :: DeBruijn' v -> Word
width Var {} = 1
width Local {} = 1
width (AppDB l r) = width l + width r
width (LamDB e) = width e

closedTerm :: F.Range Word -> F.Gen ClosedTerm
closedTerm = fmap (ClosedTerm . generaliseDB) . go 0 <=< F.integral
  where
    go !i !sz =
      if sz <= 0
        then varG
        else F.frequency [(1, varG), (1, appG), (1, lamG)]
      where
        varG
          | i > 0 = Var <$> F.int (F.between (0, i - 1))
          | otherwise = pure $ LamDB $ Var 0
        lamG =
          LamDB <$> go (i + 1) (sz - 1)
        appG = AppDB <$> go i (sz `quot` 2) <*> go i (sz `quot` 2)

newtype ClosedTerm = ClosedTerm DeBruijn

instance Show ClosedTerm where
  showsPrec d (ClosedTerm e) = showsPrec d (e :: DeBruijn' Void)

instance Eq ClosedTerm where
  (==) = (==) `on` \(ClosedTerm t) -> t :: DeBruijn' Void

instance Ord ClosedTerm where
  compare = comparing $ \(ClosedTerm t) -> t :: DeBruijn' Void
