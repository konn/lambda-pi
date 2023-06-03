{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

-- | A variant of LambdaPi syntax tree a la "<https://www.microsoft.com/en-us/research/uploads/prod/2016/11/trees-that-grow.pdf Trees That Grow>" by S. Najd and S. Peyton-Jones.
module Language.Lambda.Syntax.LambdaPi.TreesThatGrow where

import Control.Lens.Plated
import GHC.Generics (Generic, Rep)

type family XAnn phase

data Parse

data Check

data Infer

data NoExt = NoExt
  deriving (Show, Eq, Ord, Generic)

type instance XAnn Parse = NoExt

type instance XAnn Check = NoExt

type instance XAnn Infer = NoExt

type family XStar a

type instance XStar Parse = NoExt

type instance XStar Check = NoExt

type instance XStar Infer = NoExt

type family XLam a

type instance XLam Parse = Maybe (Expr Parse)

type instance XLam Check = Maybe (Expr Parse)

newtype InferLamAnn = InferLamAnn {boundVarType :: Expr Infer}
  deriving (Show, Eq, Generic)

type instance XLam Infer = InferLamAnn

data Expr phase
  = Ann (XAnn phase) (Expr phase) (Expr phase)
  | Star (XStar phase) (Expr phase) (Expr phase)
  | Lam (XLam phase) (Expr phase)
  deriving (Generic)

instance GPlated (Expr phase) (Rep (Expr phase)) => Plated (Expr phase) where
  plate = gplate
  {-# INLINE plate #-}

deriving instance
  ( Show (XAnn phase)
  , Show (XStar phase)
  , Show (XLam phase)
  ) =>
  Show (Expr phase)

deriving instance
  ( Eq (XAnn phase)
  , Eq (XStar phase)
  , Eq (XLam phase)
  ) =>
  Eq (Expr phase)

deriving instance
  ( Ord (XAnn phase)
  , Ord (XStar phase)
  , Ord (XLam phase)
  ) =>
  Ord (Expr phase)
