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

module Language.Lambda.Syntax.LambdaPi.Locals (
  Lvl (..),
  Z,
  S,
  LIdx (..),
  fromLIdx,
  predLIdx,
) where

import Data.Ord (comparing)
import GHC.Generics (Generic)
import RIO (NFData (..))

type Z = 'Z

type S = 'S

data Lvl = Z | S Lvl
  deriving (Show, Eq, Ord, Generic)
  deriving anyclass (NFData)

predLIdx :: LIdx ('S n) -> Maybe (LIdx n)
predLIdx Here = Nothing
predLIdx (There l) = Just l

data LIdx n where
  Here :: LIdx ('S n)
  There :: LIdx n -> LIdx ('S n)

instance NFData (LIdx n) where
  rnf Here = ()
  rnf (There n) = rnf n

instance Show (LIdx n) where
  showsPrec d = showsPrec d . fromLIdx

deriving instance Eq (LIdx n)

instance Ord (LIdx n) where
  compare = comparing fromLIdx

fromLIdx :: LIdx n -> Int
fromLIdx = go 0
  where
    go :: Int -> LIdx k -> Int
    go !acc Here = acc
    go acc (There n) = go (acc + 1) n
