{-# LANGUAGE GHC2021 #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE EmptyDataDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

module Data.Level (
  Lvl (..),
  SLvl (..),
  withKnownLevel,
  KnownLevel (..),
  type Z,
  type S,
  Ordinal (..),
  sLvlToOrd,
  fromOrd,
  predOrd,
  projOrd,
  injOrd,
) where

import Data.Ord (comparing)
import GHC.Exts
import GHC.Generics (Generic)
import RIO (NFData (..))
import Unsafe.Coerce (unsafeCoerce)

type Z = 'Z

type S = 'S

data Lvl = Z | S Lvl
  deriving (Show, Eq, Ord, Generic)
  deriving anyclass (NFData)

data SLvl n where
  SZ :: SLvl 'Z
  SS :: SLvl n -> SLvl ('S n)

deriving instance Show (SLvl n)

deriving instance Eq (SLvl n)

withKnownLevel :: SLvl n -> ((KnownLevel n) => act) -> act
withKnownLevel = withDict

class KnownLevel n where
  sLvl :: SLvl n

instance KnownLevel 'Z where
  sLvl = SZ

instance (KnownLevel n) => KnownLevel ('S n) where
  sLvl = SS sLvl

-- | Taking a predecessor of ordinal.
predOrd :: Ordinal ('S n) -> Maybe (Ordinal n)
predOrd Here = Nothing
predOrd (There l) = Just l

-- | Projects ordinal, which is the identity on @'Ordinal' n@ and sends @n@ to 'Nothing'.
projOrd :: SLvl n -> Ordinal ('S n) -> Maybe (Ordinal n)
projOrd SZ _ = Nothing
projOrd (SS _) Here = Just Here
projOrd (SS n) (There l) = There <$> projOrd n l

injOrd :: Ordinal n -> Ordinal ('S n)
injOrd = unsafeCoerce

-- >>> projIdx (SS (SS (SS SZ))) Here

data Ordinal n where
  Here :: Ordinal ('S n)
  There :: Ordinal n -> Ordinal ('S n)

instance NFData (Ordinal n) where
  rnf Here = ()
  rnf (There n) = rnf n

instance Show (Ordinal n) where
  showsPrec d = showsPrec d . fromOrd

deriving instance Eq (Ordinal n)

instance Ord (Ordinal n) where
  compare = comparing fromOrd

fromOrd :: Ordinal n -> Int
fromOrd = go 0
  where
    go :: Int -> Ordinal k -> Int
    go !acc Here = acc
    go acc (There n) = go (acc + 1) n

sLvlToOrd :: SLvl n -> Ordinal (S n)
sLvlToOrd SZ = Here
sLvlToOrd (SS sn) = There (sLvlToOrd sn)
