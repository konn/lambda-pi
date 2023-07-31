{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Language.Lambda.Syntax.ToySpec (test_quoteUnquote, test_thawFreeze) where

import Control.Monad ((<=<))
import qualified Data.DList as DL
import Data.Function (on)
import qualified Data.List.NonEmpty as NE
import Data.Ord (comparing)
import Data.Void (Void)
import Language.Lambda.Syntax.Toy
import qualified Test.Falsify.Generator as F
import Test.Falsify.Predicate ((.$))
import qualified Test.Falsify.Predicate as P
import Test.Falsify.Range
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

test_thawFreeze :: TestTree
test_thawFreeze = testProperty "thawLocal . freezeBound ≡ 0" $ do
  MkSomeSNat (sn :: SNat n) <- gen $ someSNat $ F.between (0, 10)
  collect "Local level" [fromSNat sn]
  t <- gen $ closedTermWithLocals (levels sn) (F.between (1, 100))
  collect "depth" [depth t]
  collect "width" [width t]
  collect "# locals" [localCount t]
  collect "local depths" $ localDepths t
  assert $
    P.eq
      .$ ("t", t :: DeBruijn' (L n))
      .$ ("thawLocal (freezeBound t)", thawLocal $ freezeBound t)

localCount :: DeBruijn' (L n) -> Int
localCount = go 0
  where
    go !acc (AppDB l r) = go (go acc l) r
    go acc (LamDB e) = go acc e
    go acc Var {} = acc
    go acc Local {} = acc + 1

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

data SomeSNat where
  MkSomeSNat :: SNat n -> SomeSNat

deriving instance Show SomeSNat

levels :: SNat n -> [L n]
levels SZ = []
levels (SS n) = Here : map There (levels n)

someSNat :: Range Word -> Gen SomeSNat
someSNat ran = toSomeSNat <$> F.integral ran

localDepths :: DeBruijn' v -> [Word]
localDepths = DL.toList . go 0
  where
    go !i (AppDB l r) = go i l <> go i r
    go _ Var {} = mempty
    go i Local {} = DL.singleton i
    go i (LamDB e) = go (i + 1) e

toSomeSNat :: Word -> SomeSNat
toSomeSNat = go
  where
    go 0 = MkSomeSNat SZ
    go n = case go (n - 1) of
      MkSomeSNat sn -> MkSomeSNat (SS sn)

closedTermWithLocals :: [v] -> F.Range Word -> F.Gen (DeBruijn' v)
closedTermWithLocals vs = go 0 <=< F.integral
  where
    go !i !sz =
      if sz <= 0
        then varOrLocalG
        else F.frequency [(1, varOrLocalG), (2, appG), (2, lamG)]
      where
        varOrLocalG = case NE.nonEmpty vs of
          Nothing -> varG
          Just ls
            | i > 0 -> rawVarG `F.choose` localG ls
            | otherwise -> localG ls
        localG ls = Local <$> F.elem ls
        rawVarG = Var <$> F.int (F.between (0, i - 1))
        varG
          | i > 0 = Var <$> F.int (F.between (0, i - 1))
          | otherwise = pure $ LamDB $ Var 0
        lamG =
          LamDB <$> go (i + 1) (sz - 1)
        appG = AppDB <$> go i (sz `quot` 2) <*> go i (sz `quot` 2)

closedTerm :: F.Range Word -> F.Gen ClosedTerm
closedTerm = fmap (ClosedTerm . generaliseDB) . closedTermWithLocals []

newtype ClosedTerm = ClosedTerm DeBruijn

instance Show ClosedTerm where
  showsPrec d (ClosedTerm e) = showsPrec d (e :: DeBruijn' Void)

instance Eq ClosedTerm where
  (==) = (==) `on` \(ClosedTerm t) -> t :: DeBruijn' Void

instance Ord ClosedTerm where
  compare = comparing $ \(ClosedTerm t) -> t :: DeBruijn' Void
