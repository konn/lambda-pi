{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE StandaloneKindSignatures #-}

module Language.Lambda.Syntax.Toy where

import Data.Kind (Type)
import Data.Sequence (Seq, (<|))
import qualified Data.Sequence as Seq
import Data.Void (Void)
import GHC.Generics (Generic)

data Nat = Z | S Nat
  deriving (Show, Eq, Ord, Generic)

data SNat n where
  SZ :: SNat 'Z
  SS :: !(SNat n) -> SNat ('S n)

deriving instance Show (SNat n)

data L n where
  Here :: L ('S n)
  There :: !(L n) -> L ('S n)

deriving instance Show (L n)

deriving instance Eq (L n)

newtype Quoted = Quoted Int
  deriving (Show, Eq, Ord, Generic)
  deriving newtype (Num)

fromSNat :: SNat n -> Int
fromSNat = go 0
  where
    go :: Int -> SNat k -> Int
    go !acc SZ = acc
    go !acc (SS n) = go (acc + 1) n

fromL :: L n -> Int
fromL = go 0
  where
    go :: Int -> L k -> Int
    go !acc Here = acc
    go !acc (There n) = go (acc + 1) n

includeL :: L n -> L ('S n)
includeL Here = Here
includeL (There i) = There (includeL i)

type HOAS' :: Type -> Type
data HOAS' v
  = AppH !(HOAS' v) !(HOAS' v)
  | LamH !(HOAS' v -> HOAS' v)
  | Quote v

type HOAS = forall v. HOAS' v

type DeBruijn = forall v. DeBruijn' v

data DeBruijn' v
  = AppDB !(DeBruijn' v) !(DeBruijn' v)
  | Var !Int
  | Local !v
  | LamDB !(DeBruijn' v)
  deriving (Show, Eq, Ord, Generic, Functor, Foldable, Traversable)

-- FIXME: We can use 'unsafeCoerce' here instead for performance.
generaliseDB :: DeBruijn' (L 'Z) -> DeBruijn
generaliseDB (AppDB l r) = generaliseDB l `AppDB` generaliseDB r
generaliseDB (Var i) = Var i
generaliseDB (LamDB e) = LamDB (generaliseDB e)

freezeBound :: DeBruijn' (L n) -> DeBruijn' (L ('S n))
freezeBound = go 0
  where
    go :: Int -> DeBruijn' (L k) -> DeBruijn' (L ('S k))
    go !i (AppDB l r) = go i l `AppDB` go i r
    go !i (Var j)
      | j == i = Local Here
      | j > i = Var $ j - 1
      | otherwise = Var j
    go !_ (Local l) = Local (There l)
    go !i (LamDB f) = LamDB $ go (i + 1) f

thawLocal :: DeBruijn' (L ('S n)) -> DeBruijn' (L n)
thawLocal = go 0
  where
    go :: Int -> DeBruijn' (L ('S n)) -> DeBruijn' (L n)
    go !i (Local Here) = Var i
    go !_ (Local (There l)) = Local l
    go !i (Var j)
      | j >= i = Var $ j + 1
      | otherwise = Var j
    go !i (AppDB l r) = go i l `AppDB` go i r
    go !i (LamDB e) = LamDB $ go (i + 1) e

unquote :: DeBruijn -> HOAS
unquote = go Seq.empty
  where
    go :: Seq (HOAS' v) -> DeBruijn' Void -> HOAS' v
    go ctx (Var i) = Seq.index ctx i
    go ctx (AppDB l r) = go ctx l `AppH` go ctx r
    go ctx (LamDB body) = LamH $ \q -> go (q <| ctx) body

quote :: Int -> HOAS' Quoted -> DeBruijn
quote i (AppH l r) = AppDB (quote i l) (quote i r)
quote i (Quote (Quoted k)) = Var $ i - k - 1
quote i (LamH f) = LamDB $ quote (i + 1) $ f (Quote $ Quoted i)
