{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE EmptyDataDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

-- | A variant of LambdaPi syntax tree a la "<https://www.microsoft.com/en-us/research/uploads/prod/2016/11/trees-that-grow.pdf Trees That Grow>" by S. Najd and S. Peyton-Jones.
module Language.Lambda.Syntax.LambdaPi.TreesThatGrow (
  -- * Phases
  Parse,
  Rename,
  Typing,
  TypingExpr (..),
  TypingMode (..),
  STypingMode (..),
  KnownTypingMode (..),
  Inferable,
  Checkable,

  -- * AST
  Name (..),
  Expr (..),
  XExpr,

  -- ** TTG types
  NoExtField (..),
  NoExtCon (),
  noExtCon,

  -- ** Field and/or Constructor extension

  -- *** Type annotation
  XAnn,
  AnnLHS,
  AnnRHS,

  -- *** Star
  XStar,

  -- *** Variables
  XVar,
  Id,
  Var (..),
  castVar,
  BoundVar,
  FreeVar,

  -- *** Application
  XApp,
  AppLHS,
  AppRHS,

  -- *** Lambda abstraction
  XLam,
  LamBindName,
  LamBindType,
  LamBody,

  -- *** Pi-types
  XPi,
  DepName (..),
  maybeName,
  PiVarName,
  PiVarType,
  PiRHS,

  -- *** Naturals
  XNat,

  -- **** constructors
  XZero,
  XSucc,
  SuccBody,

  -- **** eliminator
  XNatElim,
  NatElimRetFamily,
  NatElimBaseCase,
  NatElimInductionStep,
  NatElimInput,

  -- *** Vectors
  XVec,
  VecType,
  VecLength,

  -- **** Constructors
  XNil,
  NilType,
  XCons,
  ConsType,
  ConsLength,
  ConsHead,
  ConsTail,

  -- **** Elminator
  XVecElim,
  VecElimEltType,
  VecElimRetFamily,
  VecElimBaseCase,
  VecElimInductiveStep,
  VecElimLength,
  VecElimInput,

  -- *** Record
  XRecord,
  RecordFieldTypes (..),
  RecordFieldType,

  -- **** Constructors
  XMkRecord,
  MkRecordFields (..),
  RecordField,

  -- **** Eliminators
  XProjField,
  ProjFieldRecord,
  RecordFieldSelector,
) where

import Control.Lens.Plated
import Data.Hashable (Hashable)
import Data.Kind (Type)
import Data.Text (Text)
import GHC.Generics (Generic, Rep)
import GHC.Generics.Constraint
import RIO (NFData)

data Name = Global Text | Local Int | Quote Int
  deriving (Show, Eq, Ord, Generic)
  deriving anyclass (Hashable)

data Parse deriving (Show, Eq, Ord, Generic)

data Rename deriving (Show, Eq, Ord, Generic)

data TypingMode = Infer | Check
  deriving (Show, Eq, Ord, Generic)

data STypingMode (m :: TypingMode) where
  SInfer :: STypingMode 'Infer
  SCheck :: STypingMode 'Check

class KnownTypingMode m where
  typingModeVal :: STypingMode m

instance KnownTypingMode 'Infer where
  typingModeVal = SInfer

instance KnownTypingMode 'Check where
  typingModeVal = SCheck

data Typing (typeMode :: TypingMode)
  deriving (Show, Eq, Ord, Generic)

data NoExtField = NoExtField
  deriving (Show, Eq, Ord, Generic)

data NoExtCon
  deriving (Show, Eq, Ord, Generic)

noExtCon :: NoExtCon -> a
noExtCon = \case {}

type Inferable = Typing 'Infer

type Checkable = Typing 'Check

type family XAnn phase

type instance XAnn Parse = NoExtField

type instance XAnn Rename = NoExtField

type instance XAnn Inferable = NoExtField

type instance XAnn Checkable = NoExtCon

type family AnnLHS a

type instance AnnLHS Parse = Expr Parse

type instance AnnLHS Rename = Expr Rename

type instance AnnLHS (Typing m) = Expr Checkable

type family AnnRHS a

type instance AnnRHS Parse = Expr Parse

type instance AnnRHS Rename = Expr Rename

type instance AnnRHS (Typing m) = Expr Checkable

type family XStar p

type instance XStar Parse = NoExtField

type instance XStar Rename = NoExtField

type instance XStar Inferable = NoExtField

type instance XStar Checkable = NoExtCon

type family XVar p

type instance XVar Parse = NoExtField

type instance XVar Rename = NoExtField

type instance XVar Inferable = NoExtField

type instance XVar Checkable = NoExtCon

type family Id p

type instance Id Parse = Text

type instance Id Rename = FreeVar Rename

type instance Id (Typing m) = FreeVar (Typing m)

castVar ::
  (BoundVar p ~ BoundVar p', FreeVar p ~ FreeVar p') =>
  Var p ->
  Var p'
castVar (Bound b) = Bound b
castVar (Free b) = Free b

data Var p
  = Bound (BoundVar p)
  | Free (FreeVar p)
  deriving (Generic)

deriving instance
  (Show (BoundVar p), Show (FreeVar p)) =>
  Show (Var p)

deriving instance
  (Eq (BoundVar p), Eq (FreeVar p)) =>
  Eq (Var p)

deriving instance
  (Ord (BoundVar p), Ord (FreeVar p)) =>
  Ord (Var p)

type family BoundVar p

type instance BoundVar Parse = Text

type instance BoundVar Rename = Int

type instance BoundVar (Typing _) = Int

type family FreeVar p

type instance FreeVar Parse = Text

type instance FreeVar Rename = Name

type instance FreeVar (Typing _) = Name

type family XApp p

type instance XApp Parse = NoExtField

type instance XApp Rename = NoExtField

type instance XApp Inferable = NoExtField

type instance XApp Checkable = NoExtCon

type family AppLHS p

type instance AppLHS Parse = Expr Parse

type instance AppLHS Rename = Expr Rename

type instance AppLHS (Typing _) = Expr Inferable

type family AppRHS p

type instance AppRHS Parse = Expr Parse

type instance AppRHS Rename = Expr Rename

type instance AppRHS (Typing _) = Expr Checkable

type family XLam p

type instance XLam Parse = NoExtField

type instance XLam Rename = NoExtField

type instance XLam (Typing _) = NoExtField

type family LamBindName p

type instance LamBindName Parse = Text

type instance LamBindName Rename = Maybe Text

type instance LamBindName (Typing m) = Maybe Text

type family LamBindType p

type instance LamBindType Parse = Maybe (Expr Parse)

type instance LamBindType Rename = Maybe (Expr Rename)

type instance LamBindType Inferable = Expr Checkable

type instance LamBindType Checkable = Maybe (Expr Checkable)

type family LamBody p

type instance LamBody Parse = Expr Parse

type instance LamBody Rename = Expr Rename

type instance LamBody (Typing m) = Expr (Typing m)

type family XPi p

type instance XPi Parse = NoExtField

type instance XPi Rename = NoExtField

type instance XPi Inferable = NoExtField

type instance XPi Checkable = NoExtCon

type family PiVarName p

maybeName :: DepName -> Maybe Text
maybeName = \case
  Indep -> Nothing
  DepAnon -> Nothing
  DepNamed t -> Just t

data DepName = Indep | DepAnon | DepNamed Text
  deriving (Show, Eq, Ord, Generic)

type instance PiVarName Parse = DepName

type instance PiVarName Rename = Maybe Text

type instance PiVarName (Typing _) = Maybe Text

type family PiVarType p

type instance PiVarType Parse = Expr Parse

type instance PiVarType Rename = Expr Rename

type instance PiVarType (Typing _) = Expr Checkable

type family PiRHS p

type instance PiRHS Parse = Expr Parse

type instance PiRHS Rename = Expr Rename

type instance PiRHS (Typing _) = Expr Checkable

type family XNat p

type instance XNat Parse = NoExtField

type instance XNat Rename = NoExtField

type instance XNat Inferable = NoExtField

type instance XNat Checkable = NoExtCon

type family XZero p

type instance XZero Parse = NoExtField

type instance XZero Rename = NoExtField

type instance XZero Inferable = NoExtField

type instance XZero Checkable = NoExtCon

type family XSucc p

type instance XSucc Parse = NoExtField

type instance XSucc Rename = NoExtField

type instance XSucc Inferable = NoExtField

type instance XSucc Checkable = NoExtCon

type family SuccBody p

type instance SuccBody Parse = Expr Parse

type instance SuccBody Rename = Expr Rename

type instance SuccBody (Typing _) = Expr Checkable

type family XNatElim p

type instance XNatElim Parse = NoExtField

type instance XNatElim Rename = NoExtField

type instance XNatElim Inferable = NoExtField

type instance XNatElim Checkable = NoExtCon

type family NatElimRetFamily a

type instance NatElimRetFamily Parse = Expr Parse

type instance NatElimRetFamily Rename = Expr Rename

type instance NatElimRetFamily (Typing _) = Expr Checkable

type family NatElimBaseCase a

type instance NatElimBaseCase Parse = Expr Parse

type instance NatElimBaseCase Rename = Expr Rename

type instance NatElimBaseCase (Typing _) = Expr Checkable

type family NatElimInductionStep a

type instance NatElimInductionStep Parse = Expr Parse

type instance NatElimInductionStep Rename = Expr Rename

type instance NatElimInductionStep (Typing _) = Expr Checkable

type family NatElimInput a

type instance NatElimInput Parse = Expr Parse

type instance NatElimInput Rename = Expr Rename

type instance NatElimInput (Typing _) = Expr Checkable

type family XVec p

type instance XVec Parse = NoExtField

type instance XVec Rename = NoExtField

type instance XVec Inferable = NoExtField

type instance XVec Checkable = NoExtCon

type family VecType p

type instance VecType Parse = Expr Parse

type instance VecType Rename = Expr Rename

type instance VecType (Typing _) = Expr Checkable

type family VecLength p

type instance VecLength Parse = Expr Parse

type instance VecLength Rename = Expr Rename

type instance VecLength (Typing _) = Expr Checkable

type family XNil p

type instance XNil Parse = NoExtField

type instance XNil Rename = NoExtField

type instance XNil Inferable = NoExtField

type instance XNil Checkable = NoExtCon

type family NilType p

type instance NilType Parse = Expr Parse

type instance NilType Rename = Expr Rename

type instance NilType (Typing _) = Expr Checkable

type family XCons p

type instance XCons Parse = NoExtField

type instance XCons Rename = NoExtField

type instance XCons Inferable = NoExtField

type instance XCons Checkable = NoExtCon

type family ConsType p

type instance ConsType Parse = Expr Parse

type instance ConsType Rename = Expr Rename

type instance ConsType (Typing _) = Expr Checkable

type family ConsLength p

type instance ConsLength Parse = Expr Parse

type instance ConsLength Rename = Expr Rename

type instance ConsLength (Typing _) = Expr Checkable

type family ConsHead p

type instance ConsHead Parse = Expr Parse

type instance ConsHead Rename = Expr Rename

type instance ConsHead (Typing _) = Expr Checkable

type family ConsTail p

type instance ConsTail Parse = Expr Parse

type instance ConsTail Rename = Expr Rename

type instance ConsTail (Typing _) = Expr Checkable

type family XVecElim p

type instance XVecElim Parse = NoExtField

type instance XVecElim Rename = NoExtField

type instance XVecElim Inferable = NoExtField

type instance XVecElim Checkable = NoExtCon

type family VecElimEltType p

type instance VecElimEltType Parse = Expr Parse

type instance VecElimEltType Rename = Expr Rename

type instance VecElimEltType (Typing _) = Expr Checkable

type family VecElimRetFamily p

type instance VecElimRetFamily Parse = Expr Parse

type instance VecElimRetFamily Rename = Expr Rename

type instance VecElimRetFamily (Typing _) = Expr Checkable

type family VecElimBaseCase p

type instance VecElimBaseCase Parse = Expr Parse

type instance VecElimBaseCase Rename = Expr Rename

type instance VecElimBaseCase (Typing _) = Expr Checkable

type family VecElimInductiveStep p

type instance VecElimInductiveStep Parse = Expr Parse

type instance VecElimInductiveStep Rename = Expr Rename

type instance VecElimInductiveStep (Typing _) = Expr Checkable

type family VecElimLength p

type instance VecElimLength Parse = Expr Parse

type instance VecElimLength Rename = Expr Rename

type instance VecElimLength (Typing _) = Expr Checkable

type family VecElimInput p

type instance VecElimInput Parse = Expr Parse

type instance VecElimInput Rename = Expr Rename

type instance VecElimInput (Typing _) = Expr Checkable

type family XRecord p

type instance XRecord Parse = NoExtField

type instance XRecord Rename = NoExtField

type instance XRecord Inferable = NoExtField

type instance XRecord Checkable = NoExtCon

type family RecordFieldType p

type instance RecordFieldType Parse = Expr Parse

type instance RecordFieldType Rename = Expr Rename

type instance RecordFieldType (Typing _) = Expr Checkable

newtype RecordFieldTypes p = RecordFieldTypes {recFieldTypes :: [(Text, RecordFieldType p)]}
  deriving (Generic)

deriving instance
  Show (RecordFieldType p) => Show (RecordFieldTypes p)

deriving instance
  Eq (RecordFieldType p) => Eq (RecordFieldTypes p)

deriving instance
  Ord (RecordFieldType p) => Ord (RecordFieldTypes p)

type family XProjField p

type instance XProjField Parse = NoExtField

type instance XProjField Rename = NoExtField

type instance XProjField Inferable = NoExtField

type instance XProjField Checkable = NoExtCon

type family ProjFieldRecord p

type instance ProjFieldRecord Parse = Expr Parse

type instance ProjFieldRecord Rename = Expr Rename

type instance ProjFieldRecord (Typing _) = Expr Inferable

type family RecordFieldSelector p

type instance RecordFieldSelector Parse = Text

type instance RecordFieldSelector Rename = Text

type instance RecordFieldSelector (Typing p) = Text

type family XMkRecord p

type instance XMkRecord Parse = NoExtField

type instance XMkRecord Rename = NoExtField

type instance XMkRecord (Typing _) = NoExtField

type family RecordField p

type instance RecordField Parse = Expr Parse

type instance RecordField Rename = Expr Rename

type instance RecordField (Typing m) = Expr (Typing m)

newtype MkRecordFields p = MkRecordFields {mkRecFields :: [(Text, RecordField p)]}
  deriving (Generic)

deriving instance Show (RecordField p) => Show (MkRecordFields p)

deriving instance Eq (RecordField p) => Eq (MkRecordFields p)

deriving instance Ord (RecordField p) => Ord (MkRecordFields p)

deriving anyclass instance NFData (RecordField p) => NFData (MkRecordFields p)

deriving anyclass instance Hashable (RecordField p) => Hashable (MkRecordFields p)

type family XExpr p

type instance XExpr Parse = NoExtCon

type instance XExpr Rename = NoExtCon

type instance XExpr (Typing m) = TypingExpr m

type TypingExpr :: TypingMode -> Type
data TypingExpr m where
  BVar :: Int -> TypingExpr 'Infer
  Inf :: Expr Inferable -> TypingExpr 'Check

deriving instance Show (TypingExpr m)

deriving instance Eq (TypingExpr m)

deriving instance Ord (TypingExpr m)

data Expr phase
  = Ann (XAnn phase) (AnnLHS phase) (AnnRHS phase)
  | Star (XStar phase)
  | Var (XVar phase) (Id phase)
  | App (XApp phase) (AppLHS phase) (AppRHS phase)
  | Lam (XLam phase) (LamBindName phase) (LamBindType phase) (LamBody phase)
  | Pi (XPi phase) (PiVarName phase) (PiVarType phase) (PiRHS phase)
  | Nat (XNat phase)
  | Zero (XZero phase)
  | Succ (XSucc phase) (SuccBody phase)
  | NatElim
      (XNatElim phase)
      (NatElimRetFamily phase)
      (NatElimBaseCase phase)
      (NatElimInductionStep phase)
      (NatElimInput phase)
  | Vec (XVec phase) (VecType phase) (VecLength phase)
  | Nil (XNil phase) (NilType phase)
  | Cons (XCons phase) (ConsType phase) (ConsLength phase) (ConsHead phase) (ConsTail phase)
  | VecElim
      (XVecElim phase)
      (VecElimEltType phase)
      (VecElimRetFamily phase)
      (VecElimBaseCase phase)
      (VecElimInductiveStep phase)
      (VecElimLength phase)
      (VecElimInput phase)
  | Record (XRecord phase) (RecordFieldTypes phase)
  | MkRecord (XMkRecord phase) (MkRecordFields phase)
  | ProjField (XProjField phase) (ProjFieldRecord phase) (RecordFieldSelector phase)
  | XExpr (XExpr phase)
  deriving (Generic)

instance GPlated (Expr phase) (Rep (Expr phase)) => Plated (Expr phase) where
  plate = gplate
  {-# INLINE plate #-}

deriving instance FieldC Show (Expr phase) => Show (Expr phase)

deriving instance FieldC Eq (Expr phase) => Eq (Expr phase)

deriving instance FieldC Ord (Expr phase) => Ord (Expr phase)

deriving anyclass instance FieldC Hashable (Expr phase) => Hashable (Expr phase)
